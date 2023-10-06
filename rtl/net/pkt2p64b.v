////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/pkt2p64b.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Converts from our AXI network protocol to the 64bit payload
//		required by the PCS layer in the IEEE standard, while bypassing
//	the XGMII layer in the process.
//
//	Why bypass the 32-bit XGMII?  1) Because the Xilinx PHY operates at
//	64-bits at a time, not 32.  2) Because the 64b/66b encoder requires
//	64 bits at a time.  Other projects still call this an XGMII interface.
//	This interface is close, though not quite there, since the IEEE
//	requires XSGMII to be 32-bits per cycle.
//
//	By convention, ethernet sends the two sync bits first, followed by
//	bit 0 of byte 0 first.  This IP, therefore, assumes a little endian
//	byte order, with S_DATA[7:0] being the *first* byte in any packet.
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
// }}}
module	pkt2p64b (
		// {{{
		input	wire		TX_CLK, S_ARESETN,
		//
		input	wire		i_remote_fault, i_local_fault,
		//
		input	wire		S_VALID,
		output	wire		S_READY,
		input	wire	[63:0]	S_DATA,
		input	wire	[2:0]	S_BYTES,
		input	wire		S_LAST,
		input	wire		S_ABORT,
		//
		// output wire		TXVALID=1 is assumed
		// Ideally, we wouldn't need TXREADY, *but* the FPGA operates
		// at a faster clock rate (at one clock per 64 outputs, not
		// 1 clock per 66 inputs), so we need it here.
		input	wire		TXREADY,
		output	reg	[65:0]	TXDATA
		// }}}
	);

	// Local declarations
	// {{{
	localparam [1:0]	TX_IDLE     = 2'h0,
				TX_DATA     = 2'h1,
				TX_LAST     = 2'h2,
				TX_PAUSE    = 2'h3;
	localparam [1:0]	SYNC_CONTROL = 2'b01,
				SYNC_DATA    = 2'b10;

	localparam	[65:0]	P_IDLE  = { {(8){7'h07}},
						CW(8'h1e), SYNC_CONTROL },
			// Indicate a remote fault
			P_FAULT = { 8'h02, 16'h0, 8'h0, 8'h02, 16'h0,
						CW(8'h55), SYNC_CONTROL },
			// Start a packet--always on a 64b boundary
			P_START = { 8'h5d, {(6){8'h55}},
						CW(8'h78), SYNC_CONTROL },
			P_LAST  = { {(8){7'h00}},
						CW(8'h87), SYNC_CONTROL };
	//
	// "They [idles] shall not be added while data is being received.  When
	// deleting /I/s, the first four characters after a /T/ shall not be
	// deleted.

	reg		r_ready, flushing;
	reg	[1:0]	state;

	reg		stretch_fault;
	reg	[7:0]	stretch_counter;
	reg		r_aborted;

	reg		r_local_fault, r_remote_fault;
	(* ASYNC_REG = "TRUE" *) reg	[1:0]	r_local_fault_pipe,
						r_remote_fault_pipe;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Fault CDC and stretching
	// {{{

	// Local faults
	// {{{
	always @(posedge TX_CLK)
	if (!S_ARESETN)
		{ r_local_fault, r_local_fault_pipe } <= 0;
	else
		{ r_local_fault, r_local_fault_pipe }
				<= { r_local_fault_pipe, i_local_fault };
	// }}}

	// Remote faults -> stretch_fault
	// {{{
	always @(posedge TX_CLK)
	if (!S_ARESETN)
		{ r_remote_fault, r_remote_fault_pipe } <= 0;
	else
		{ r_remote_fault, r_remote_fault_pipe }
				<= { r_remote_fault_pipe, i_remote_fault };

	initial	stretch_fault   = 0;
	initial	stretch_counter = 0;
	always @(posedge TX_CLK)
	if (!S_ARESETN)
	begin
		stretch_fault <= 0;
		stretch_counter <= 0;
	end else if (r_remote_fault)
	begin
		stretch_fault   <= 1;
		stretch_counter <= -1;
	end else begin
		if (stretch_counter > 0)
			stretch_counter <= stretch_counter - 1;
		stretch_fault <= (stretch_counter > 1);
	end
	// }}}
	// }}}

	// abort stretching
	// {{{
	always @(posedge TX_CLK)
	if (!S_ARESETN || TXREADY)
		r_aborted <= 1'b0;
	else if (S_ABORT)
		r_aborted <= 1'b1;
	// }}}

	initial	r_ready = 1'b0;
	initial	TXDATA  = P_IDLE;
	always @(posedge TX_CLK)
	if (!S_ARESETN)
	begin
		// {{{
		r_ready <= 1'b0;
		state   <= TX_IDLE;
		TXDATA  <= P_IDLE;
		flushing <= 1'b0;
		// }}}
	end else if (r_local_fault || flushing || stretch_fault
					|| r_remote_fault)
	begin
		// {{{
		if (TXREADY)
		begin
			if (r_local_fault)
				TXDATA <= P_FAULT;
			else
				TXDATA <= P_IDLE;
		end

		if (state == TX_DATA || r_ready)
			flushing <= 1'b1;

		state  <= TX_PAUSE;

		if (S_VALID && S_READY && S_LAST)
		begin
			r_ready <= 1'b0;
			state   <= TX_PAUSE;
			flushing<= 1'b0;
		end else // Flush any ongoing packet
			r_ready <= flushing || (state == TX_DATA);
		// }}}
	end else case(state)
	TX_IDLE: begin
		// {{{
		r_ready <= 1'b0;
		TXDATA <= P_IDLE;
		if (S_VALID)
		begin
			if (!S_ABORT && TXREADY)
			begin
				state  <= TX_DATA;
				TXDATA <= P_START;
				r_ready <= 1'b1;
			end else begin
				// Accept the ABORT flag and continue
				r_ready <= S_ABORT && !r_ready;
			end
		end end
		// }}}
	TX_DATA: begin
		// {{{
		r_ready <= 1'b1;
		if (TXREADY)
		begin
			TXDATA  <= { S_DATA, SYNC_DATA };
			if (S_ABORT || r_aborted || !S_VALID)
			begin
				// ERROR!!  Send error code, then terminate
				state   <= TX_PAUSE;
				TXDATA  <= P_FAULT;
				r_ready <= 1'b0;
				flushing <= !S_VALID && !S_ABORT && !r_aborted;
			end else if (S_LAST)
			begin
				r_ready <= 1'b0;
				state <= TX_PAUSE;
				case(S_BYTES)
				3'h0: state <= TX_LAST;
				3'h1: TXDATA <= { 48'h0000_0000_0000,
					S_DATA[7:0], CW(8'h99), SYNC_CONTROL };
				3'h2: TXDATA <= { 40'h0000_0000_00,
					S_DATA[15:0], CW(8'haa), SYNC_CONTROL };
				3'h3: TXDATA <= { 32'h0000_0000, S_DATA[23:0],
						CW(8'hb4), SYNC_CONTROL };
				3'h4: TXDATA <= { 24'h0000_00,
					S_DATA[31:0], CW(8'hcc), SYNC_CONTROL };
				3'h5: TXDATA <= { 16'h0000,
					S_DATA[39:0], CW(8'hd2), SYNC_CONTROL };
				3'h6: TXDATA <= { 8'h00,
					S_DATA[47:0], CW(8'he1), SYNC_CONTROL };
				3'h7: TXDATA <= {
					S_DATA[55:0], CW(8'hff), SYNC_CONTROL};
				// No default needed
				endcase
			end
		end else if (S_ABORT)
		begin
			r_ready <= 1'b0;
		end end
		// }}}
	TX_LAST: begin
		// {{{
		r_ready <= 1'b0;
		if (TXREADY)
		begin
			TXDATA  <= P_LAST;
			state   <= TX_PAUSE;
		end end
		// }}}
	TX_PAUSE: begin // Ensure interframe gaps
		// {{{
		r_ready <= 1'b0;
		if (TXREADY)
		begin
			TXDATA <= P_IDLE;
			state <= TX_IDLE;
		end end
		// }}}
	// default: begin end
	endcase

	assign	S_READY = r_ready && (TXREADY || flushing);

	function automatic [7:0] CW(input [7:0] in);
		// {{{
		integer	cwik;
	begin
		for(cwik=0; cwik<8; cwik=cwik+1)
			CW[cwik] = in[7-cwik];
	end endfunction
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	wire	[10:0]	fs_word;
	wire	[12-1:0]	fs_packets;
	(* keep *) wire	[63:0]		ftx_data;
	(* keep *) wire	[1:0]		ftx_sync;
	(* keep *) wire	[7:0]		ftx_control;

	initial	f_past_valid = 1'b0;
	always @(posedge TX_CLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(!S_ARESETN);

	assign	ftx_data    = TXDATA[65:2];
	assign	ftx_control = TXDATA[9:2];
	assign	ftx_sync    = TXDATA[1:0];

	////////////////////////////////////////////////////////////////////////
	//
	// Input stream properties
	// {{{
	faxin_slave #(
		.DATA_WIDTH(64)
	) faxin (
		// {{{
		.S_AXI_ACLK(TX_CLK), .S_AXI_ARESETN(S_ARESETN),
		//
		.S_AXIN_VALID(S_VALID),
		.S_AXIN_READY(S_READY),
		.S_AXIN_DATA(S_DATA),
		.S_AXIN_BYTES(S_BYTES),
		.S_AXIN_LAST(S_LAST),
		.S_AXIN_ABORT(S_ABORT),
		//
		.f_stream_word(fs_word), .f_packets_rcvd(fs_packets)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output 66b protocol
	// {{{

	// Our one assumption--TXREADY will be usually true, but may drop for
	// one cycle, and one cycle only, every now and then
	always @(posedge TX_CLK)
	if (!$past(TXREADY))
		assume(TXREADY);

	always @(posedge TX_CLK)
	if (!S_ARESETN || !$past(S_ARESETN))
	begin
		assert(!S_ARESETN || TXDATA == P_IDLE);
	end else if (!$past(TXREADY))
		assert($stable(TXDATA));
	else if (($past(TXDATA[1:0]) == SYNC_CONTROL)
					&&($past(TXDATA) != P_START))
		assert(TXDATA[1:0] == SYNC_CONTROL);

	always @(posedge TX_CLK)
	if (S_ARESETN)
	begin
		assert(^TXDATA[1:0]);
		if (TXDATA[1:0] == SYNC_CONTROL)
		begin
			case(TXDATA[9:2])
			CW(8'h1e): assert(TXDATA == P_IDLE);
			CW(8'h55): assert(TXDATA == P_FAULT);
			CW(8'h78): assert(TXDATA == P_START);
			CW(8'h87): assert(TXDATA == P_LAST);
			//
			CW(8'h99): assert(TXDATA[65:18] == 0);
			CW(8'haa): assert(TXDATA[65:26] == 0);
			CW(8'hb4): assert(TXDATA[65:34] == 0);
			CW(8'hcc): assert(TXDATA[65:42] == 0);
			CW(8'hd2): assert(TXDATA[65:50] == 0);
			CW(8'he1): assert(TXDATA[65:58] == 0);
			CW(8'hff): begin end
			default: assert(0);
			endcase
		end
	end

	always @(posedge TX_CLK)
	if ($past(TXREADY && TXDATA == P_START))
		assert(TXDATA != P_START);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract
	// {{{
	(* anyconst *)	reg	fc_check;
	(* anyconst *)	reg	[10:0]	fc_posn;
	(* anyconst *)	reg	[63:0]	fc_data;
	(* anyconst *)	reg	[2:0]	fc_bytes;
	(* anyconst *)	reg		fc_last, fnvr_local, fnvr_abort;
	reg		f_eop;
	reg	[10:0]	fpkt_word;

	// Assume a known/valid input, with a known word of data
	// {{{
	// Note we have to be careful to caveat all of our assumptions to
	// only take hold when fc_check is true.  This is the case where we
	// assume an uninterrupted packet input.  It may not truly be the
	// case, however.  Therefore, we must allow for !fc_check, and only
	// make these assumptions when fc_check is true.
	always @(*)
	if (!fc_last)
		assume(fc_bytes == 0);

	// Incoming stream *MUST* remain valid for a packet to be successful
	always @(posedge TX_CLK)
	if (S_ARESETN && $past(S_ARESETN) && fc_check
					&& $past(S_VALID && !S_LAST))
		assume(S_VALID);

	always @(posedge TX_CLK)
	if (S_ARESETN && $past(S_ARESETN) && fc_check && S_VALID)
		assume(!S_ABORT);

	always @(*)
	if (S_ARESETN && fc_check && fs_word < fc_posn && S_VALID)
		assume(!S_LAST);

	always @(*)
	if (S_ARESETN && fc_check && fc_posn == fs_word && S_VALID)
	begin
		assume(S_DATA  == fc_data);
		assume(S_BYTES == fc_bytes);
		assume(S_LAST  == fc_last);
	end

	always @(*)
	if (fnvr_abort)
		assume(!S_ABORT);

	always @(*)
	if (S_ARESETN && fnvr_abort)
		assert(!r_aborted);

	always @(*)
	if (fnvr_local)
		assume(!i_local_fault);

	always @(*)
	if (fc_check)
		assume(fnvr_local);

	always @(*)
	if (fc_check)
		assume(fnvr_abort);

	// This won't work if faults take place, so let's assume no faults
	// during our special check packet
	always @(*)
	if (fc_check)
		assume((fpkt_word == 0 && state==TX_IDLE) || !r_remote_fault);
	// }}}

	always @(*)
	if (TXDATA[1:0] != SYNC_CONTROL)
		f_eop = 1'b0;
	else case(TXDATA[9:2])
		CW(8'h99): f_eop = 1'b1;
		CW(8'haa): f_eop = 1'b1;
		CW(8'hb4): f_eop = 1'b1;
		CW(8'hcc): f_eop = 1'b1;
		CW(8'hd2): f_eop = 1'b1;
		CW(8'he1): f_eop = 1'b1;
		CW(8'hff): f_eop = 1'b1;
		P_LAST[9:2]: f_eop = 1'b1;
		default: f_eop = 1'b0;
	endcase

	always @(posedge TX_CLK)
	if (!S_ARESETN || flushing)
	begin
		fpkt_word <= 0;
	end else if (TXREADY)
	begin
		if (TXDATA == P_START || TXDATA == P_IDLE)
			fpkt_word <= 0;
		else if (TXDATA[1:0] == SYNC_DATA)
			fpkt_word <= fpkt_word + 1;
		else if (f_eop)
			fpkt_word <= 0;
	end

	always @(posedge TX_CLK)
	if (S_ARESETN && !flushing && !stretch_fault && !r_remote_fault)
	begin
		if (fs_word > 0)
		begin
			assert(fs_word == fpkt_word + 1);
		end else if (!f_eop && state != TX_LAST)
			assert(fpkt_word == 0 || !fnvr_local || !fnvr_abort);
	end

	// Contract assertion
	always @(posedge TX_CLK)
	if (S_ARESETN && fc_check && fc_posn > 0)
	begin
		if (TXDATA[1:0]== SYNC_DATA)
		begin
			if (fpkt_word == fc_posn)
			begin
				assert(TXDATA[65:2] == fc_data);
				assert(!fc_last || fc_bytes == 0);
			end

			if (fc_last)
				assert(fpkt_word <= fc_posn);
		end else if (fpkt_word == fc_posn
						&& TXDATA[1:0] == SYNC_CONTROL)
		begin
			assert(fc_last && fc_bytes != 0);
			case(TXDATA[9:2])
			CW(8'h99): assert(TXDATA[17:10] == fc_data[7:0]);
			CW(8'haa): assert(TXDATA[25:10] == fc_data[15:0]);
			CW(8'hb4): assert(TXDATA[33:10] == fc_data[23:0]);
			CW(8'hcc): assert(TXDATA[41:10] == fc_data[31:0]);
			CW(8'hd2): assert(TXDATA[49:10] == fc_data[39:0]);
			CW(8'he1): assert(TXDATA[57:10] == fc_data[47:0]);
			CW(8'hff): assert(TXDATA[65:10] == fc_data[55:0]);
			default: begin end
			endcase
		end else if (fc_last)
		begin
			if (fpkt_word == fc_posn + 1)
			begin
				assert(fc_last && fc_bytes == 0);
				assert(f_eop && TXDATA == P_LAST);
			end else if (fc_posn > 0)
				assert(fpkt_word < fc_posn);
		end
	end

	always @(*)
	if (S_ARESETN && fnvr_local)
		assert(!r_local_fault);

	always @(*)
	if (S_ARESETN && fc_check && fpkt_word > 0)
	begin
		assert(!flushing);
		assert(!stretch_fault);
	end

	always @(*)
	if (S_ARESETN && !flushing && !r_aborted)
	case(state)
	TX_IDLE: assert(fs_word == 0);
	TX_DATA: begin
		assert(r_ready != r_aborted);
		assert((fs_word == fpkt_word + 1) || TXDATA == P_START
			|| S_ABORT);
		end
	TX_LAST: assert(fs_word == 0);
	TX_PAUSE: assert(fs_word == 0);
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover
	// {{{

	always @(posedge TX_CLK)
	if (S_ARESETN && $past(S_ARESETN))
		cover(TXDATA[1:0] == SYNC_DATA);

	always @(posedge TX_CLK)
	if (S_ARESETN && $past(S_ARESETN) && TXDATA[1:0] == SYNC_CONTROL)
	begin
		case(TXDATA[9:2])
		CW(8'h1e): cover(1);
		CW(8'h55): cover(1);
		CW(8'h78): cover(1);
		CW(8'h87): cover(1);
		//
		CW(8'h99): cover(1);
		CW(8'haa): cover(1);
		CW(8'hb4): cover(1);
		CW(8'hcc): cover(1);
		CW(8'hd2): cover(1);
		CW(8'he1): cover(1);
		CW(8'hff): cover(1);
		endcase
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{

	// The following assumption simply prevents overflow in our packet word
	// counting math.  The number of bits used to count words could be
	// increased arbitrarily if we desired.  That would just increase the
	// bit used in the assumption below.
	always @(*)
		assume(!fs_word[10]);
	// }}}
`endif
// }}}
endmodule
