////////////////////////////////////////////////////////////////////////////////
//
// Filename:	tbenet.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Models a 10Gb 10GBASE-R Ethernet, at 64'bits of data at a time.
//		Input is an AXI network stream that must never run dry
//	mid-packet.  Output is an abortable AXI network stream.  The goal is to
//	be an *all* Verilog model, for the ultimate purpose of testing/verifying
//	a 10Gb Ethernet configuration of the GTX transceivers on the Xilinx
//	7-series FPGAs--or at least the Kintex version among them.
//
//	Note that this module *GENERATES* clocks for use in the test bench
//	IP--both for the receive and transmit links.  Use a cross clock module
//	(axincdc.v) and possibly a FIFO (netfifo.v) if you need to interact
//	with another clock.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023, Gisselquist Technology, LLC
// {{{
// This file is part of the ETH10G project.
//
// The ETH10G project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
// }}}
//	http://www.apache.org/licenses/LICENSE-2.0
// {{{
// Unless required by applicable law or agreed to in writing, files
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
`timescale	1ns / 1fs
// }}}
module	tbenet (
		// {{{
`ifdef	VERILATOR
		input	wire		oversampled_clk,
`endif
		input	wire		i_cfg_bypass_scrambler,
		// Input comes from an external packet generator source
		// {{{
		output	wire		S_CLK,
		output	reg		S_RESETn,
		input	wire		S_VALID,
		output	wire		S_READY,
		input	wire	[31:0]	S_DATA,
		input	wire	[1:0]	S_BYTES,
		input	wire		S_FAULT,	// Src fault indicator
		input	wire		S_LAST,
		// }}}
		// IO headed to/from the GTX transceiver(s)
		// {{{
		output	wire		o_tx,
		input	wire		i_rx,
		// }}}
		// Outgoing AXI network stream to the packet scoreboard
		// {{{
		output	wire		M_CLK,
		output	reg		M_RESETn,
		output	reg		M_VALID,
		input	wire		M_READY,
		output	reg	[63:0]	M_DATA,
		output	reg	[2:0]	M_BYTES,
		output	reg		M_ABORT, M_LAST
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam [0:0]	OPT_REVERSE_CW = 1'b0;
	localparam	OVERSAMPLE_RATIO = 8;
	// Verilator lint_off WIDTH
	localparam [$clog2(OVERSAMPLE_RATIO)-1:0] OVM1 = OVERSAMPLE_RATIO-1;
	// Verilator lint_on  WIDTH
	localparam	BSMSB = 18;

	localparam	[6:0]	IDL = 7'h00;
	localparam	[1:0]	SYNC_CONTROL = 2'b01,
				SYNC_DATA    = 2'b10;
	localparam [65:0]	PKTPREFIX= { 8'hd5, {(6){8'h55}},
						CW(8'h78), SYNC_CONTROL },
				PKTHALFPREFIX = {
					24'h55_55_55, 4'b00,
					{(4){IDL}},
					CW(8'h33), SYNC_CONTROL },
				PKTFAULTSTART = { 24'h55_55_55, 4'h0,
					{(4){IDL}}, CW(8'h66), SYNC_CONTROL },
	//
				PKTFAULT={ 24'h02_0000, 8'h00,
					24'h02_0000, CW(8'h55), SYNC_CONTROL },
				PKTFAULTLFT={ 24'h02_0000, 4'h0,
					{(4){IDL}}, CW(8'h2d), SYNC_CONTROL },
				PKTFAULTRHT={ {(4){IDL}}, 4'h0,
					24'h02_0000, CW(8'h4b), SYNC_CONTROL },
	//
				PKTEOP  ={ {(8){IDL}},CW(8'h87), SYNC_CONTROL },
				PKTIDLE  ={ {(8){IDL}},CW(8'h1e), SYNC_CONTROL };
	localparam	[31:0]	PKT_SOP = 32'hd5_55_55_55;

`ifdef	VERILATOR
	wire					txclk;
`else
	localparam real	BAUD_PERIOD = 1.0 / (10.0 * 66/64); // in fraction of ns
	localparam real	OVERSAMPLE_PERIOD = BAUD_PERIOD / OVERSAMPLE_RATIO;

	reg					txclk;
	reg					oversampled_clk;
`endif
	integer					ip;
	reg	[2*OVERSAMPLE_RATIO-1:0]	rxsreg;
	reg					rxsqrd;
	reg	[BSMSB:0]		rxsubavg [0:OVM1];
	reg	signed [BSMSB+$clog2(OVERSAMPLE_RATIO):0]	bsmatch, bsmatchacc,
						last_bsmatch;
	reg					bsrise;
	reg	[$clog2(OVERSAMPLE_RATIO)-1:0]	ckphase;
	wire	[$clog2(OVERSAMPLE_RATIO)-1:0]	ck_offset;
	reg					cklocked;
	wire					sample_clk;
	reg	[3:0]				m_reset_pipe,
						s_reset_pipe;
	reg	[1:0]	spkt_active;
	reg		spkt_half, spkt_fault;
	reg	[57:0]	rxfill;
	reg	[65:0]	rxword, rxpay, prerxpay,
			last_rx_payload, last_tx_payload;
	reg	[6:0]	rxwphase;
	reg		rxwlock, rxmatch;
	reg	[3:0]	rxwlock_count;
	reg		rxw_valid;

	reg		pl_state, pl_valid, pl_last, pl_fault;
	reg	[3:0]	pl_bytes;
	reg	[63:0]	pl_data;
	reg		pl_started, pl_half, pl_offset;
	reg	[31:0]	pl_mem;

	reg	[57:0]	txfill, nextfill;
	reg	[65:0]	txsreg, nexttx, txpay;
	reg	[6:0]	spos;
	reg	[2:0]	new_txbytes;

	reg		eop, pending_eop;
	reg		spkt_last;
	wire  	stxstb;
	reg	[1:0]	spkt_bytes;
	reg	[31:0]	spkt_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// RX Clock/Reset generation / recovery, bit sync
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

`ifndef	VERILATOR
	initial	oversampled_clk = 0;
	always
		#(OVERSAMPLE_PERIOD / 2.0) oversampled_clk = !oversampled_clk;
`endif

	// 1. Multiply the input by the input, 1/4 baud later
	initial	begin
		rxsreg = 0;
		rxsqrd = 0;
		for(ip=1; ip<OVERSAMPLE_RATIO; ip=ip+1)
			rxsubavg[ip] = 0;
	end

	always @(posedge oversampled_clk)
	begin
		rxsreg <= { rxsreg[2*OVERSAMPLE_RATIO-2:0], (i_rx === 1'b1) };
		// rxsqrd: A cyclic autocorrelation measure
		rxsqrd <= (i_rx === 1'b1) ^ rxsreg[OVERSAMPLE_RATIO/2-1];

		// rxsubavg[]: Provide for some tracking historesis
		// {{{
		// Goal here is to "average" what should be a (near) sine
		// wave at a period of OVERSAMPLE_RATIO.
		//
		for(ip=1; ip<OVERSAMPLE_RATIO; ip=ip+1)
		begin
			rxsubavg[ip] <= rxsubavg[ip-1];
			/*
			if (rxsubavg[ip-1] != 0)
				rxsubavg[ip] <= rxsubavg[ip-1] - 1;
			else
				rxsubavg[ip] <= 0;
			*/
		end

		if (rxsqrd === 1'b1)
		begin
			if (rxsubavg[OVM1] + 64 >= (1<<BSMSB))
				rxsubavg[0] <= (1<<BSMSB);
			else
				rxsubavg[0] <= rxsubavg[OVM1] + 64;
		end else if (rxsubavg[OVM1] > 1)
			rxsubavg[0] <= rxsubavg[OVM1] - 1;
		else
			rxsubavg[0] <= 0;
		// }}}
	end

	// Find the center of the baud: apply a crude filter, look for the max
	// {{{
	// bsmatchacc = The output of the crude (matched?) filter
	// Here, for a filter, we're using an 8-sample triangle wave.
	//	Coefficients are: 2, 1, 0, -1, -2, -1, 0, 1
	always @(*)//rxsubavg[0])
	begin
		// Verilator lint_off WIDTH
		bsmatchacc = 0;
		for(ip=0; ip<OVERSAMPLE_RATIO; ip=ip+1)
		begin
			if (ip == 0)
				bsmatchacc = bsmatchacc + 2 * rxsubavg[ip];
			else if (ip == OVERSAMPLE_RATIO/4)
			begin end
			else if (ip == OVERSAMPLE_RATIO/2)
				bsmatchacc = bsmatchacc - 2 * rxsubavg[ip];
			else if (ip == 3*OVERSAMPLE_RATIO/4)
			begin end
			else if (ip < OVERSAMPLE_RATIO/4)
				bsmatchacc = bsmatchacc + rxsubavg[ip];
			else if (ip == OVERSAMPLE_RATIO/4)
			begin end
			else if (ip < 3*OVERSAMPLE_RATIO/4)
				bsmatchacc = bsmatchacc - rxsubavg[ip];
			else if (ip == 3*OVERSAMPLE_RATIO/4)
			begin end
			else
				bsmatchacc = bsmatchacc + rxsubavg[ip];
		end
		// Verilator lint_on  WIDTH
	end

	// Clock in the result of our matched filter
	always @(posedge oversampled_clk)
	if (!M_RESETn)
		bsmatch <= 0;
	else
		bsmatch <= bsmatchacc;

	// Hill climb to the best match
	initial	last_bsmatch = 0;
	always @(posedge oversampled_clk)
		last_bsmatch <= bsmatch;

	// Have we found the highest point?
	initial	bsrise = 0;
	always @(posedge oversampled_clk)
		bsrise <= (bsmatch > last_bsmatch)
				|| (bsrise && bsmatch == last_bsmatch);
	// }}}

	// Lock to this center, and generate an outgoing clock
	// {{{
	// CAN'T RESET HERE, since our reset depends on the clock we are
	// generating using this logic
	initial	ckphase  = 0;
	initial	cklocked = 0;
	always @(posedge oversampled_clk)
	if (bsrise && (bsmatch < last_bsmatch))
	begin
		cklocked <= (ckphase == OVM1) || (ckphase == 0)
				|| (ckphase == OVM1-1) || (ckphase == OVM1-2);
		ckphase <= 0;
	end else begin
		ckphase <= ckphase + 1;
	end

	assign	ck_offset  = ckphase + 5;
	assign	sample_clk = ck_offset[$clog2(OVERSAMPLE_RATIO)-1];

	assign	M_CLK = sample_clk;
	// }}}

	// M_RESET, M_ABORT, via asynchronous reset synchronizer
	// {{{
	initial	{ M_RESETn, m_reset_pipe } = 0;
	always @(posedge sample_clk)
		{ M_RESETn, m_reset_pipe } <= { m_reset_pipe, 1'b1 };

	always @(posedge sample_clk or negedge cklocked)
	if (!cklocked)
		M_ABORT = 1'b1;
	else if (!M_VALID || M_READY)
		M_ABORT <= 1'b0;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchonize to 66 bit RX words
	// {{{

	// Shift register(s), to receive the incoming data
	// {{{
	initial	{ rxword, rxfill } = 0;
	always @(posedge sample_clk)
	begin
		rxword <= { i_rx, rxword[65:1] };
		rxfill <= { rxfill[56:0], rxword[0] };
	end
	// }}}

	// Synchronization state machine ...

	always @(*)
		prerxpay = DESCRAMBLE({ rxfill[56:0], rxword[0] },
					{ i_rx, rxword[65:1] });

// {{{
	(* keep *) reg	[7:0]	rxdbg_count;
	(* keep *) reg	[65:0]	rxdbg_data;
	initial	rxdbg_count = 0;
	always @(posedge sample_clk)
	if (rxdbg_count >= 65)
		rxdbg_count <= 0;
	else
		rxdbg_count <= rxdbg_count + 1;

	always @(posedge sample_clk)
	if (rxdbg_count == 0)
		rxdbg_data <= rxword;
// }}}

	// rxmatch
	// {{{
	// rxmatch = ... could this descrambled word be a valid 66B encoded wrd?
	initial	rxmatch = 0;
	always @(*)
	if (rxwphase != 0 || rxword[2] == rxword[1])
		// rxwphase != 0 means we're counting 66b from the last match
		// If rxword[2] == rxword[1], then we have a 66b/64b coding
		// violation.
		rxmatch = 1'b0;
	else if (rxword[2:1] == SYNC_CONTROL)
	begin
		// Look for valid codewords.  If it's not a valid codeword,
		// it can't be a valid match.
		case(prerxpay[9:2])
		CW(8'h1e): rxmatch = 1'b1;
		CW(8'h2d): rxmatch = 1'b1;
		CW(8'h33): rxmatch = 1'b1;
		CW(8'h66): rxmatch = 1'b1;
		CW(8'h55): rxmatch = 1'b1;
		CW(8'h78): rxmatch = 1'b1;
		CW(8'h4b): rxmatch = 1'b1;
		CW(8'h87): rxmatch = 1'b1;
		CW(8'h99): rxmatch = 1'b1;
		CW(8'haa): rxmatch = 1'b1;
		CW(8'hb4): rxmatch = 1'b1;
		CW(8'hcc): rxmatch = 1'b1;
		CW(8'hd2): rxmatch = 1'b1;
		CW(8'he1): rxmatch = 1'b1;
		CW(8'hff): rxmatch = 1'b1;
		default: rxmatch = 1'b0;
		endcase
	end else
		// All data words are valid
		rxmatch = 1'b1;
	// }}}

	// rxwphase, rxwlock, rxwlock_count
	// {{{
	// Now that we have rxmatch to tell us when we might match, let's try
	// to track that on a 66bit basis, such that every 66b we have a match
	// if all goes well.
	initial	rxwphase = 0;
	initial	rxwlock_count = 0;
	initial	rxwlock = 0;
	always @(posedge sample_clk)
	if (M_ABORT)
	begin
		rxwphase <= 0;
		rxwlock  <= 0;
		rxwlock_count <= 0;
	end else if (rxwphase == 0)
	begin
		if (!rxmatch)
		begin
			// Unlocked.  Look for a potential match
			// {{{
			rxwphase <= 0;	// Keep us in this state, searching.

			rxwlock_count <= 0;
			rxwlock <= 1'b0;
			/*
			if (rxwlock_count > 0)
				rxwlock_count  <= rxwlock_count - 1;
			else
				rxwlock <= 1'b0;
			*/
			// }}}
		end else begin	// MATCH!
			// {{{
			rxwphase <= 1;	// Count bits until the next max
			if (!(&rxwlock_count))
				rxwlock_count <= rxwlock_count + 1;
			else	// If we've matched for a while, declare a lock
				rxwlock <= 1'b1;
			// }}}
		end
	end else if (rxwphase < 65)
		rxwphase <= rxwphase + 1;
	else
		// We've seen 66 bits, now wrap back to 0
		rxwphase <= 0;
	// }}}

	// rxw_valid -- true when we've captured a valid word
	// {{{
	initial	rxw_valid = 1'b0;
	always @(posedge sample_clk or negedge cklocked)
	if (!cklocked)
		rxw_valid <= 1'b0;
	else if (!rxwlock)
		rxw_valid <= 1'b0;
	else
		rxw_valid <= (rxwphase == 0);
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// RX Packet generation
	// {{{

	// pl*: Take a clock for last generation and offset handling
	// {{{
	// Remember, Ethernet works on "End-of-Packet" markers that show up
	// one byte after the last valid data.  In order to convert this to
	// AXI packet stream, we need to make sure the LAST goes with the last
	// word of data.  That means we'll need to delay everything by one
	// word, lest there be an EOP marker received with no data attached.

	// pl_state: Are we somewhere within a valid packet?
	// {{{
	always @(posedge sample_clk)
	if (!M_RESETn || M_ABORT)
		pl_state <= 1'b0;
	else if (rxw_valid && (rxpay == PKTPREFIX
				|| rxpay == PKTHALFPREFIX
				|| rxpay == PKTFAULTSTART))
		pl_state <= 1'b1;
	else if (rxw_valid && rxpay[1:0] != SYNC_DATA)
		pl_state <= 1'b0;
	// }}}

	// pl_offset, pl_half
	// {{{
	// pll_offset is true on the first word of an off-cut packet.  This
	//	is to keep us from calling it valid.
	// pll_half is true throughout an off-cut packet, so we can be sure
	//	to grab the last half-word from our buffer at the end of the
	//	packet.
	always @(posedge sample_clk)
	if (!M_RESETn || M_ABORT)
		{ pl_offset, pl_half } <= 2'b0;
	else if (rxw_valid)
	begin
		if (rxpay == PKTPREFIX)
			{ pl_offset, pl_half } <= 2'b00;
		else if (rxpay == PKTHALFPREFIX || rxpay == PKTFAULTSTART)
			{ pl_offset, pl_half } <= 2'b11;
		else if (rxw_valid && !pl_state && pl_half)
			{ pl_offset, pl_half } <= { 1'b0, (pl_half && pl_bytes>0)};
		else if (rxpay[1:0] != SYNC_DATA && !pl_started)
			// Clear the offset and half for all other controls
			{ pl_offset, pl_half } <= 2'b00;
		else
			pl_offset <= 1'b0;
	end
	// }}}

	// pl_valid
	// {{{
	// pl_valid -- do we have something valid in our buffer?
	always @(posedge sample_clk)
	if (!M_RESETn)
		pl_valid <= 1'b0;
	else if (rxw_valid)
		pl_valid <= pl_state && !pl_offset && (rxpay[9:0] != PKTEOP[9:0]);
	// }}}

	// rxpay is the payload, once it's been descrambled.
	always @(*)
		rxpay = DESCRAMBLE(rxfill, rxword);

	// And ... the massive state machine
	always @(posedge sample_clk)
	if (!M_RESETn || M_ABORT)
	begin
		pl_started <= 1'b0;	// True if we are in a packet
		pl_data   <= 64'b0;	// Buffered data
		pl_mem    <= 32'b0;	// Used if we are off cut by 32b
		pl_bytes  <= 0;		// Bytes in our buffer, modulo 8
		pl_last   <= 1'b0;	// Is the buffer the last data?
		pl_fault  <= 1'b0;	// Has there been a fault of some type?

		last_rx_payload <= 66'h0;;
	end else if (rxw_valid)
	begin
		last_rx_payload <= rxpay;
		pl_fault <= 1'b0;
		pl_last  <= (pl_bytes > 0);
		pl_bytes <= (pl_bytes[3]) ? { 1'b0, pl_bytes[2:0] }: 4'h0;
		{ pl_data, pl_mem } <= { 64'h0, pl_data[63:32] };
		if (rxpay[1:0] == SYNC_DATA)
		begin
			// {{{
			pl_last  <= 0;
			if (!pl_started)
			begin
				{ pl_data, pl_mem } <= 96'h0;
				pl_bytes <= 4'h0;
			end else if (pl_half)
			begin
				{ pl_data, pl_mem } <= {
						rxpay[65:2], pl_data[63:32] };
				pl_bytes <= (pl_offset) ? 4'h0 : 4'h4;
			end else begin
				{ pl_data, pl_mem } <= { rxpay[65:2], 32'h0 };
				pl_bytes <= 4'h8;
			end
			// }}}
		end else case(rxpay[9:2])	// Decode the control codes
		CW(8'h1e): begin	// C0-C7
			// {{{
			pl_started <= 0;
			// pl_mem   <= 0;
			// pl_data  <= 0;
			// pl_bytes <= 0;
			end
			// }}}
		CW(8'h2d): begin	// C0-C3, FAULT
			// {{{
			pl_started <= 0;
			pl_mem   <= 0;
			pl_data  <= 0;
			// pl_bytes <= 0;
			// pl_last  <= 0;
			pl_fault <= 1;
			end
			// }}}
		CW(8'h33): begin	// C0-C3, START
			// {{{
			pl_started <= 1;
			pl_mem   <= 0;
			pl_data  <= 0;
			// pl_bytes <= 0;
			end
			// }}}
		CW(8'h66): begin	// FAULT, START
			// {{{
			pl_started <= 1;
			pl_mem   <= 0;
			pl_data  <= 0;
			pl_bytes <= 0;
			end
			// }}}
		CW(8'h55): begin	// FAULT, FAULT
			// {{{
			pl_started <= 0;
			pl_mem   <= 0;
			pl_data  <= 0;
			// pl_bytes <= 0;
			// pl_last  <= 0;
			pl_fault <= !pl_half;
			end
			// }}}
		CW(8'h78): begin	// START
			// {{{
			pl_started <= 1;
			pl_mem   <= 0;
			pl_data  <= rxpay[63:0];
			pl_bytes <= 0;
			pl_last  <= 0;
			end
			// }}}
		CW(8'h4b): begin	// FAULT, C4-C7
			// {{{
			pl_started <= 0;
			pl_mem   <= 0;
			pl_data  <= 0;
			pl_bytes <= 0;
			pl_last  <= 0;
			end
			// }}}
		CW(8'h87): begin	// T0, C0-C7
			// {{{
			pl_started <= 0;
			if (pl_half)
				pl_mem <= pl_data[63:32];
			else
				pl_mem <= 32'h0;
			pl_last  <= 1;
			pl_data  <= 64'h0;

			pl_bytes <= pl_bytes;
			end
			// }}}
		CW(8'h99): begin	// D0, T1, C2-C7
			// {{{
			pl_started <= 1;
			pl_mem   <= 0;

			if (pl_half)
				{ pl_data, pl_mem } <= { 56'h0, rxpay[17:10], pl_data[63:32] };
			else
				{ pl_data, pl_mem } <= { 56'h0, rxpay[17:10], 32'h0};

			pl_bytes <= pl_bytes[2:0] + 4'h1;
			pl_last  <= 1'b1;
			end
			// }}}
		CW(8'haa): begin	// D0-D1, T2, C3-C7
			// {{{
			if (pl_half)
				{ pl_data, pl_mem } <= { 48'h0, rxpay[25:10], pl_data[63:32] };
			else
				{ pl_data, pl_mem } <= { 48'h0, rxpay[25:10], 32'h0};

			pl_bytes <= pl_bytes[2:0] + 4'h2;
			pl_last  <= 1'b1;
			end
			// }}}
		CW(8'hb4): begin	// D0-D2, T3, C4-C7
			// {{{
			if (pl_half)
				{ pl_data, pl_mem } <= { 40'h0, rxpay[33:10], pl_data[63:32] };
			else
				{ pl_data, pl_mem } <= { 40'h0, rxpay[33:10], 32'h0};
			pl_bytes <= pl_bytes[2:0] + 4'h3;
			pl_last  <= 1'b1;
			end
			// }}}
		CW(8'hcc): begin	// D0-D3, T4, C5-C7
			// {{{
			if (pl_half)
				{ pl_data, pl_mem } <= { 32'h0, rxpay[41:10], pl_data[63:32] };
			else
				{ pl_data, pl_mem } <= { 32'h0, rxpay[41:10], 32'h0};
			pl_bytes <= pl_bytes[2:0] + 4'h4;
			pl_last  <= 1'b1;
			end
			// }}}
		CW(8'hd2): begin	// D0-D4, T5, C6-C7
			// {{{
			if (pl_half)
				{ pl_data, pl_mem } <= { 24'h0, rxpay[49:10], pl_data[63:32] };
			else
				{ pl_data, pl_mem } <= { 24'h0, rxpay[49:10], 32'h0};
			pl_bytes <= pl_bytes[2:0] + 4'h5;
			pl_last  <= !pl_half;
			end
			// }}}
		CW(8'he1): begin	// D0-D5, T6, C7
			// {{{
			if (pl_half)
				{ pl_data, pl_mem } <= { 16'h0, rxpay[57:10], pl_data[63:32] };
			else
				{ pl_data, pl_mem } <= { 16'h0, rxpay[57:10], 32'h0};
			pl_bytes <= pl_bytes[2:0] + 4'h6;
			pl_last  <= !pl_half;
			end
			// }}}
		CW(8'hff): begin	// D0-D6, T7
			// {{{
			if (pl_half)
				{ pl_data, pl_mem } <= { 8'h0, rxpay[65:10], pl_data[63:32] };
			else
				{ pl_data, pl_mem } <= { 8'h0, rxpay[65:10], 32'h0};
			pl_bytes <= pl_bytes[2:0] + 4'h7;
			pl_last  <= !pl_half;
			end
			// }}}
		default: begin
			// {{{
			pl_started <= 0;
			pl_mem   <= 0;
			pl_data  <= 0;
			pl_bytes <= 0;
			pl_last  <= 0;
			pl_fault <= 1;
			end
			// }}}
		endcase
	end
	// }}}

	// M_* Packet generation
	// {{{
	// Now, turn those pl_* signals into an actual outgoing packet.

	always @(posedge sample_clk or negedge M_RESETn)
	if (!M_RESETn)
		M_VALID <= 1'b0;
	else if (rxw_valid)
		M_VALID <= pl_valid || (pl_half && pl_bytes > 0);
	else
		M_VALID <= 1'b0;

	always @(posedge sample_clk)
	if (rxw_valid)
	begin
		if (pl_half)
			// If we are off cut, we have to grab data from one
			// word earlier to finish our outgoing data word.
			M_DATA <= { pl_data[31:0], pl_mem };
		else
			M_DATA <= pl_data;
	end

	always @(posedge sample_clk or negedge M_RESETn)
	if (!M_RESETn)
	begin
		M_LAST <= 0;
		M_BYTES <= 0;
	end else if (rxw_valid)
	begin
		M_LAST  <= (pl_last && pl_bytes <= 4'h8)
				|| (!pl_half && rxpay[9:0] == { CW(8'h87), SYNC_CONTROL });
		M_BYTES <= (pl_last && pl_bytes <= 4'h8) ? pl_bytes[2:0] : 3'h0;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// TX Clock/Reset generation
	// {{{

	// In order to be able to support starting halfway through a 64-bit
	// word, we need to use a 32-bit interface.

	// txclk generation at 10.3125 Gb/s
	// {{{
	// First, let's generate an arbitrary clock.  This clock may (or may
	// not) match the other clocks along the way.  It just needs to be
	// within "tolerance" (whatever that actually is ...)
`ifdef	VERILATOR
	reg	[$clog2(OVERSAMPLE_RATIO)-1:0]	txctr;

	initial	txctr = 0;
	always @(posedge oversampled_clk)
		txctr <= txctr + 1;

	assign	txclk = txctr[$clog2(OVERSAMPLE_RATIO)-1];
`else
	initial	txclk = 0;
	always
		txclk = #(BAUD_PERIOD/2.0) !txclk;
`endif
	// }}}

	initial	{ S_RESETn, s_reset_pipe } = 0;
	always @(posedge txclk)
		{ S_RESETn, s_reset_pipe } <= { s_reset_pipe, 1'b1 }; 

	// stxstb, once every 33 clocks
	// {{{
	initial	spos = 0;
	always @(posedge txclk)
	if (!S_RESETn)
		spos <= 0;
	else if (spos >= 32)
		spos <= 0;
	else
		spos <= spos + 1;

	assign	stxstb = (spos >= 32);
	// }}}

	// spkt_half, every other stxstb
	// {{{
	initial	spkt_half = 0;
	always @(posedge txclk)
	if (!S_RESETn)
		spkt_half <= 0;
	else if (stxstb)
		spkt_half <= !spkt_half;
	// }}}

	// spkt_active
	// {{{
	initial	spkt_active = 2'b00;
	always @(posedge txclk)
	if (!S_RESETn)
		spkt_active <= 2'b00;
	else if (stxstb)
	begin
		if (spkt_half && S_VALID && S_READY && S_LAST)
			spkt_active <= 2'b00;
		else
			spkt_active<= { spkt_active[0], (S_VALID && !S_FAULT) };
	end
	// }}}

	assign	S_READY = stxstb && S_RESETn && !eop
					&& ((&spkt_active) || S_FAULT);

	// spkt_fault: Did we fault on the first half cycle?
	// {{{
	always @(posedge txclk)
	if (!S_RESETn)
		spkt_fault <= 0;
	else if (stxstb)
		// Always clear after the second half cycle
		spkt_fault <= S_FAULT && !spkt_half;
	// }}}

	// spkt_bytes, spkt_data, spkt_last
	// {{{
	always @(posedge txclk)
	if (!S_RESETn)
	begin
		spkt_bytes <= 0;
		spkt_data  <= 0;
		spkt_last  <= 0;
	end else if (stxstb)
	begin
		if (spkt_half)
		begin
			// Always clear a packet on the second half cycle.
			spkt_bytes <= 0;
			spkt_data  <= 0;
			spkt_last  <= 0;
		end else if (S_VALID && S_READY && !S_FAULT)
		begin
			spkt_bytes <= S_BYTES[1:0];
			spkt_data  <= S_DATA;
			spkt_last  <= S_LAST;
			if (S_BYTES == 0)
				spkt_bytes <= 2'b00;
		end else if (S_VALID || S_FAULT)
		begin // Prepare for beginning the next packet
			spkt_data  <= PKT_SOP;
			spkt_bytes <= 2'h0;
		end
	end
	// }}}

	// txpay
	// {{{
	// Transmit payload.  Given our buffered 32b, generate an outgoing
	// 66b codeword.
	always @(*)
	begin
		new_txbytes = ((spkt_bytes == 2'b00) ? 3'h4 : {1'b0,spkt_bytes})
			+((S_VALID && S_READY) ? ((S_BYTES[1:0] == 2'b00) ? 3'h4
					: { 1'b0, S_BYTES[1:0] }) : 3'h0);
		pending_eop = 0;

		txpay = PKTIDLE;
		if (!spkt_half || !stxstb)
			txpay = 66'h0;
		else if (eop)
			txpay = PKTEOP;
		else if ((S_VALID && S_READY && !S_FAULT)
				|| (!S_FAULT && spkt_active[1]==1'b1))
		begin // Within a data packet
			// {{{
			if (S_VALID && !S_LAST) // In the middle of a packet
				txpay = { S_DATA, spkt_data, SYNC_DATA };
			else case(new_txbytes[2:0])	// Finish a packet
			0:begin
				txpay={ S_DATA,spkt_data, SYNC_DATA };
				pending_eop = 1;		// == S_LAST
				end
			1:txpay={{(6){IDL}},6'h0,spkt_data[ 7:0],CW(8'h99), SYNC_CONTROL };
			2:txpay={{(5){IDL}},5'h0,spkt_data[15:0],CW(8'haa), SYNC_CONTROL };
			3:txpay={{(4){IDL}},4'h0,spkt_data[23:0],CW(8'hb4), SYNC_CONTROL };
			4:txpay={{(3){IDL}},3'h0,spkt_data[31:0],CW(8'hcc), SYNC_CONTROL };
			5:txpay={{(2){IDL}},2'b00, S_DATA[ 7:0], spkt_data, CW(8'hd2), SYNC_CONTROL };
			6:txpay={IDL,1'b0,S_DATA[15:0],spkt_data,CW(8'he1), SYNC_CONTROL };
			7:txpay={       S_DATA[23:0], spkt_data, CW(8'hff), SYNC_CONTROL };
			endcase
			// }}}
		end else if (S_VALID || S_FAULT) // && !eop && S_FAULT
		begin
			// {{{
			case({ spkt_fault, S_FAULT })
			2'b00: if (spkt_active == 2'b01)	// && S_VALID
					txpay = PKTPREFIX;	// Full PKT strt
				else
					txpay = PKTHALFPREFIX;	// CTRL, STRT
			2'b01: txpay = PKTFAULTLFT;
			2'b10: txpay = PKTFAULTSTART;
			2'b11: txpay = PKTFAULT;
			endcase
			// }}}
		end else if (spkt_fault)
			txpay = PKTFAULTRHT;
		else
			txpay = PKTIDLE;

		// Now that we know the codeword, we can scramble it.
		{ nextfill, nexttx } = SCRAMBLE(txfill, txpay);
	end
	// }}}

	// eop
	// {{{
	always @(posedge txclk)
	if (!S_RESETn)
		eop <= 0;
	else if (stxstb && spkt_half)
		eop <= pending_eop && S_VALID;
	// }}}

	always @(posedge txclk)
	if (!S_RESETn)
		last_tx_payload <= 0;
	else if (stxstb && spkt_half)
		last_tx_payload <= txpay;

	// o_tx, txfill, txsreg
	// {{{
	// Register the scrambled transmit codeword, and then shift it out
	// one bit at a time.
	always @(posedge txclk)
	if (!S_RESETn)
		{ txfill, txsreg } <= { {(58){1'b1}}, 66'h0 };
	else if (stxstb && spkt_half)
		{ txfill, txsreg } <= { nextfill, nexttx };
	else
		txsreg <= { 1'b0, txsreg[65:1] };

	assign	o_tx = txsreg[0];
	// }}}

	assign	S_CLK = txclk;
	// }}}

	function automatic [58+66-1:0] SCRAMBLE(input [57:0] fill,
		 // {{{
						input [65:0] data);
		integer		pos;
		reg	[57:0]	rfill;
		reg	[65:0]	out;
	begin
		rfill = fill;
		out   = data;
		for(pos=2; pos<66; pos=pos+1)
		begin
			out[pos] = rfill[57] ^ rfill[38] ^ data[pos];
			rfill = { rfill[56:0], out[pos] };
			if (i_cfg_bypass_scrambler)
				out[pos] = data[pos];
		end

		SCRAMBLE = { rfill, out };
	end endfunction
	// }}}

	function automatic [66-1:0] DESCRAMBLE(input [57:0] fill,
		 // {{{
						input [65:0] data);
		integer		pos;
		reg	[57:0]	rfill;
		reg	[65:0]	out;
	begin
		rfill = fill;
		out   = data;
		for(pos=2; pos<66; pos=pos+1)
		begin
			if (i_cfg_bypass_scrambler)
				out[pos] = data[pos];
			else
				out[pos] = rfill[57] ^ rfill[38] ^ data[pos];
			rfill = { rfill[56:0], data[pos] };
		end

		DESCRAMBLE = out;
	end endfunction
	// }}}

	function automatic [7:0] CW(input [7:0] in);
		// {{{
		integer	cwik;
	begin
		if (OPT_REVERSE_CW)
		begin
			for(cwik=0; cwik<8; cwik=cwik+1)
				CW[cwik] = in[7-cwik];
		end else
			CW = in;
	end endfunction
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, prerxpay[65:10], prerxpay[1:0],
				rxsreg };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
