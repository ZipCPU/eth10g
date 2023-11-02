////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/p642pkt.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Convert from the format at the output of the PHY (66 bits
//		per clock) to an outgoing AXI network packet protocol.
//
//	Note that because Xilinx GTX will be generating 66-bits at a time,
//	we're skipping the 32-bit XGMII interface and going directly from a
//	66-bit interface to a 64-bit AXI network interface.
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
`default_nettype none
// }}}
module	p642pkt #(
		parameter [0:0]	OPT_REVERSE_CW = 1'b0
	) (
		// {{{
		input	wire		RX_CLK, S_ARESETN,
		//
		input	wire		i_phy_fault,
		output	reg		o_remote_fault,
		output	wire		o_local_fault,
		output	wire		o_link_up,
		//
		input	wire		RX_VALID,
		input	wire	[65:0]	RX_DATA,
		//
		output	reg		M_VALID,
		input	wire		M_READY,
		output	reg	[63:0]	M_DATA,
		output	reg	[2:0]	M_BYTES,
		output	reg		M_ABORT,
		output	reg		M_LAST
		// }}}
	);

	// Local declarations
	// {{{
	localparam 	[1:0]	SYNC_CONTROL	= 2'b01,
				SYNC_DATA	= 2'b10;
	localparam		PRE_IDLE = 1'b0,
				PRE_DATA = 1'b1;

	localparam	[65:0]	R_PREAMBLE = { 32'h5d55_5555, 24'h5555_55,
						CW(8'h78), SYNC_CONTROL },
			R_HALF_PREAMBLE1= { 24'h5555_55,4'h0,28'h0000_00,
						CW(8'h33), SYNC_CONTROL },
			R_HALF_PREAMBLE2= { 24'h5555_55,4'h0,28'h0000_00,
						CW(8'h66), SYNC_CONTROL },
			R_HALF_MASK = { 24'hff_ffff, 4'h0, 28'h000_0000,
						CW(8'hff), 2'b11 };
			// R_IDLE = { 32'h00000000, 32'h0000001e,
			//				SYNC_CONTROL },
			// R_LPIDLE = { 32'h06060606, 32'h0606061e,
			//				SYNC_CONTROL };
	localparam	[23:0]	REMOTE_FAULT = { 8'h02, 8'h00, 8'h00 };
	localparam		LNKMSB = 26;

	reg		pstate, phalf, poffset;

	reg		dly_valid, dly_last;
	reg	[63:0]	dly_data;
	reg	[31:0]	dly_half;
	reg	[3:0]	dly_bytes;

	// Fault detection registers
	reg		r_local_fault;
	reg	[6:0]	watchdog_counter;
	reg		watchdog_timeout;
	reg	[LNKMSB:0]	link_up_counter;

	reg			max_packet_fault;
	reg	[18:0]		max_packet_counter;

	reg			powering_up;
	reg	[3:0]		stretch_local;
	reg			stretch_fault;
	// }}}

	// Processing steps:
	// (0) Unscramble the payload
	// 1. Unpack control and data characters
	// 2. Check control characters for validity
	// 3. Classify packets
	// 4. Generate START/STOP characters
	// 5. Pack data words
	// 6. Generate LAST and flush the packing circuit

	// Cross clock domains
	(* ASYNC_REG = "TRUE" *)	reg		r_fault;
	(* ASYNC_REG = "TRUE" *)	reg	[1:0]	r_fault_pipe;
	initial	{ r_fault, r_fault_pipe } = -1;
	always @(posedge RX_CLK)
	if (!S_ARESETN)
		{ r_fault, r_fault_pipe } <= -1;
	else
		{ r_fault, r_fault_pipe } <= { r_fault_pipe, i_phy_fault };

	// pstate
	// {{{
	always @(posedge RX_CLK)
	if (!S_ARESETN || r_fault || M_ABORT || powering_up || r_local_fault)
		pstate <= PRE_IDLE;
	else if (RX_VALID)
	case(pstate)
	PRE_IDLE: begin
		// {{{
		pstate <= PRE_IDLE;
		if (RX_DATA == R_PREAMBLE
			|| ((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE1)
			|| ((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE2))
			pstate <= PRE_DATA;
		if ((dly_last || poffset) || (M_VALID && !M_READY))
			// Output is still hung with the previous packet.
			// Drop this one and wait for the next preamble.
			pstate <= PRE_IDLE;
		end
		// }}}
	PRE_DATA: begin
		if (RX_DATA[1:0] == SYNC_DATA)
			pstate <= PRE_DATA;
		// else if (RX_DATA == R_IDLE)
		//	pstate <= PRE_DATA;
		else
			pstate <= PRE_IDLE;
		end
	endcase
	// }}}

	// phalf, poffset
	// {{{
	// phalf   == discard the first half of the next word.
	// poffset == we are off-set from true.  Each new data word will bring
	//	four bytes to output, and four bytes to reserve for the next
	//	cycle.
	always @(posedge RX_CLK)
	if (!S_ARESETN || r_fault || M_ABORT)
		{ phalf, poffset } <= 2'b00;
	else if (RX_VALID)
	case(pstate)
	PRE_IDLE: begin
		// {{{
		if ((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE1)
			{ phalf, poffset } <= 2'b11;
		else if ((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE2)
			{ phalf, poffset } <= 2'b11;
		else
			{ phalf, poffset } <= 2'b00;
		end
		// }}}
	PRE_DATA: phalf <= 1'b0;
	endcase else if ((!M_VALID || M_READY) && dly_last)
		{ phalf, poffset } <= 2'b00;
`ifdef	FORMAL
	always @(*)
	if (S_ARESETN && !poffset)
		assert(!phalf);
`endif
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// dly_*: The delay stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// We need this stage because XGMII sends an "end-of-packet" indicator
	// one byte after the last character, whereas our AXI-network protocol
	// is supposed to guarantee M_LAST on the last beat of the packet.
	// Hence, if the "end-of-packet" character shows up on byte-0, then
	// we'd set M_LAST one beat too late if we didn't have this delay stage.

	// One problem: there's no guarantee of receiving 8-bytes per clock.
	// The following assuming we either have 8-bytes per clock or its the
	// last beat in the packet.  The protocol doesn't require this.  Rather,
	// the protocol only requires 4-bytes per beat, allowing for the other
	// 4-bytes to be stuff bytes (i.e. idles, either low-power or otherwise)
	// in order to deal with clock mismatch issues.

	// Not quite.  It's illegal to send IDLEs during a packet.  If the
	// transmitted can't keep up with the packet, the packet will be
	// ABORTed.  (Otherwise, we might be confuse an all IDLE control stream
	// with a response to an remote_fault packet.)

	// During an packet, we should be able to expect code words:
	// ALL DATA
	// 8'h87
	// 8'h99
	// 8'haa
	// 8'hb4
	// 8'hcc
	// 8'hd2
	// 8'he1
	// 8'hff
	// All but the all-data control word indicate the end of the packet.
	// Any other control words will need to result in an aborted packet

	// dly_valid
	// {{{
	always @(posedge RX_CLK)
	if (!S_ARESETN || r_fault || r_local_fault || powering_up || M_ABORT)
		dly_valid <= 0;
	else if (RX_VALID)
	begin
		if (RX_DATA[1:0] == SYNC_DATA)
			dly_valid <= pstate;
		else if (RX_DATA[1:0] != SYNC_CONTROL)
			dly_valid <= 1'b0;
		else if (RX_DATA[9:2] == CW(8'h87))
			// Unless this is a completely control frame,
			// we're valid
			dly_valid <= poffset;
		else
			dly_valid <= pstate;

		if (pstate != PRE_DATA)
			dly_valid <= (dly_bytes > 8);
		else if (phalf)
			dly_valid <= 1'b0;
	end else if (dly_last && (!M_VALID || M_READY))
		dly_valid <= dly_valid && (dly_bytes > 8);
	// }}}

	// dly_half
	// {{{
	// Since it's posible for a packet to start on a half-64-bit boundary,
	// we need a bit of a gearbox to realign the packet back onto a 64bit
	// boundary.  dly_half is where we stuff that extra data.
	always @(posedge RX_CLK)
	if (!S_ARESETN || !poffset || r_fault || r_local_fault || M_ABORT)
		dly_half <= 0;
	else if (RX_VALID)
	begin
		dly_half <= RX_DATA[65:34];	// D4, D5, D6, D7

		// If the word is a control word, then we're offset, based upon
		// the 8'bits necessary to specify the type of control word.
		// That puts our first bit at (2+32+8 = 42), not 34.  So, let's
		// adjust that here.
		if (RX_DATA[1:0] == SYNC_CONTROL)
		case(RX_DATA[9:2])
		// CW(8'h99):
		// CW(8'haa):
		// CW(8'hb4):
		// CW(8'hcc):
		CW(8'hd2): dly_half <= { 24'h0, RX_DATA[49:42] };
		CW(8'he1): dly_half <= { 16'h0, RX_DATA[57:42] };
		CW(8'hff): dly_half <= {  8'h0, RX_DATA[65:42] };
		default: dly_half <= 32'h0;
		endcase
	end
	// }}}

	// dly_data
	// {{{
	always @(posedge RX_CLK)
	if (!S_ARESETN || r_fault || r_local_fault)
		dly_data <= 0;
	else if (RX_VALID && !dly_last)
	begin
		if (poffset)
		begin // Gearbox.  Use 32-bits from before, and up to 32-bits
			// {{{
			// from the current word
			dly_data <= { RX_DATA[33:2], dly_half };
			if (RX_DATA[1:0] == SYNC_CONTROL)
			case(RX_DATA[9:2])
			CW(8'h99): dly_data[63:32] <= { 24'h0, RX_DATA[17:10] };
			CW(8'haa): dly_data[63:32] <= { 16'h0, RX_DATA[25:10] };
			CW(8'hb4): dly_data[63:32] <= {  8'h0, RX_DATA[33:10] };
			CW(8'hcc): dly_data[63:32] <= {        RX_DATA[41:10] };
			// The rest of these have more than 32bits defined,
			// but we only need 32 of the incoming bits.  The other
			// 32bits will be in dly_half for the next clock cycle.
			CW(8'hd2): dly_data[63:32] <= {        RX_DATA[41:10] };
			CW(8'he1): dly_data[63:32] <= {        RX_DATA[41:10] };
			CW(8'hff): dly_data[63:32] <= {        RX_DATA[41:10] };
			default: dly_data[63:32] <= 32'h0;
			endcase
			// }}}
		end else begin // No gearbox, direct map 64bits to output
			// {{{
			dly_data <= RX_DATA[65:2];
			if (RX_DATA[1:0] == SYNC_CONTROL)
			case(RX_DATA[9:2])
			CW(8'h99): dly_data <= { 56'h0, RX_DATA[17:10] };
			CW(8'haa): dly_data <= { 48'h0, RX_DATA[25:10] };
			CW(8'hb4): dly_data <= { 40'h0, RX_DATA[33:10] };
			CW(8'hcc): dly_data <= { 32'h0, RX_DATA[41:10] };
			CW(8'hd2): dly_data <= { 24'h0, RX_DATA[49:10] };
			CW(8'he1): dly_data <= { 16'h0, RX_DATA[57:10] };
			CW(8'hff): dly_data <= {  8'h0, RX_DATA[65:10] };
			default: begin end
			endcase

			if (pstate != PRE_DATA)
				dly_data <= 0;
			// }}}
		end
	end else if (dly_valid && dly_last)
		dly_data <= { 32'h0, dly_half };
	// }}}

	// dly_bytes
	// {{{
	// Number of valid bytes in the delay cell.
	always @(posedge RX_CLK)
	if (!S_ARESETN || r_fault || r_local_fault || M_ABORT)
		dly_bytes <= 0;
	else if (RX_VALID && !dly_last)
	begin
		// if (!pstate && RX_DATA[9:0] == { 8'h78, SYNC_CONTROL })
		//	dly_bytes <= 0;
		// else if (!pstate && RX_DATA[9:0] == { 8'h78, SYNC_CONTROL })
		//	dly_bytes <= 0;

		if (phalf)
			dly_bytes <= 4;	// These bytes are in dly_half
		else if (poffset)
		begin
			// {{{
			dly_bytes <= 12;	// dly_half + dly_data
			if (RX_DATA[1:0] == SYNC_CONTROL)
			case(RX_DATA[9:2])
			CW(8'h87): dly_bytes <= 4'd4 + 4'd0;
			CW(8'h99): dly_bytes <= 4'd4 + 4'd1;
			CW(8'haa): dly_bytes <= 4'd4 + 4'd2;
			CW(8'hb4): dly_bytes <= 4'd4 + 4'd3;
			CW(8'hcc): dly_bytes <= 4'd4 + 4'd4;
			CW(8'hd2): dly_bytes <= 4'd4 + 4'd5;
			CW(8'he1): dly_bytes <= 4'd4 + 4'd6;
			CW(8'hff): dly_bytes <= 4'd4 + 4'd7;
			default: begin end
			endcase

			if (pstate != PRE_DATA)
				dly_bytes<=(dly_bytes <= 8) ? 0 : (dly_bytes-8);
			// }}}
		end else if (pstate)
		begin
			dly_bytes <= 4'd8;	// 64 incoming bits => 8bytes
			if (RX_DATA[1:0] == SYNC_CONTROL)
			case(RX_DATA[9:2])
			CW(8'h99): dly_bytes <= 4'd1;
			CW(8'haa): dly_bytes <= 4'd2;
			CW(8'hb4): dly_bytes <= 4'd3;
			CW(8'hcc): dly_bytes <= 4'd4;
			CW(8'hd2): dly_bytes <= 4'd5;
			CW(8'he1): dly_bytes <= 4'd6;
			CW(8'hff): dly_bytes <= 4'd7;
			default: begin end
			endcase
		end else
			dly_bytes <= 0;
	end else if (dly_valid && dly_last)
		dly_bytes <= (dly_last && dly_bytes > 8) ? (dly_bytes - 8) : 0;
	else if (!dly_valid)
		dly_bytes <= 0;
`ifdef	FORMAL
	always @(*)
	if (S_ARESETN && dly_valid && !dly_last)
		assert(dly_bytes[2] == poffset);
`endif
	// }}}

	// dly_last
	// {{{
	always @(posedge RX_CLK)
	if (!S_ARESETN || r_fault || r_local_fault || M_ABORT)
		dly_last <= 0;
	else if (RX_VALID && !dly_last)
	begin
		dly_last <= 1'b0;
		if (pstate != PRE_DATA)
			dly_last <= 1'b1; // poffset;
		else if (RX_DATA[1:0] == SYNC_CONTROL)
			dly_last <= 1'b1; // (RX_DATA[9:2] != 8'h87);

		if (!dly_valid)
			dly_last <= 1'b0;
	end else if (!M_VALID || M_READY)
		dly_last <= !pstate && dly_valid && (dly_bytes > 8);
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Fault detection
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// Local & Remote fault detection
	// {{{
	// These faults are all determined by the data sent.  If no data
	// gets sent, or if we never lock (and hence RX_VALID stays low),
	// then we'll never know a fault

	reg	past_stop;

	initial	past_stop = 1'b0;
	always @(posedge RX_CLK)
	if (!S_ARESETN)
		past_stop <= 1'b0;
	else if (RX_VALID)
	begin
		past_stop <= (RX_DATA[1:0] != SYNC_DATA);
		/*
		if (RX_DATA[1:0] != SYNC_CONTROL)
			past_stop <= 1'b0;
		else case(RX_DATA[9:2])
		// 8'h1e: r_local_fault <= 1'b0;
		// 8'h2d: r_local_fault <= (RX_DATA[65:42] != REMOTE_FAULT);
		// 8'h33: r_local_fault <= 1'b0;
		// 8'h66: r_local_fault <= (RX_DATA[33:10] != REMOTE_FAULT);
		// 8'h55: r_local_fault <= (RX_DATA[65:42] != REMOTE_FAULT);
		// 8'h78: r_local_fault <= 1'b0;
		// 8'h4b: r_local_fault <= (RX_DATA[33:10] != REMOTE_FAULT);
		CW(8'h87): past_stop <= 1'b1;
		CW(8'h99): past_stop <= 1'b1;
		CW(8'haa): past_stop <= 1'b1;
		CW(8'hb4): past_stop <= 1'b1;
		CW(8'hcc): past_stop <= 1'b1;
		CW(8'hd2): past_stop <= 1'b1;
		CW(8'he1): past_stop <= 1'b1;
		CW(8'hff): past_stop <= 1'b1;
		default: past_stop <= 1'b0;
		endcase
		*/
	end

	always @(posedge RX_CLK)
	if (!S_ARESETN)
	begin
		o_remote_fault <= 1'b0;
		r_local_fault  <= 1'b0;
	end else if (RX_VALID)
	begin
		case(RX_DATA[9:2])
		CW(8'h2d): o_remote_fault <= (RX_DATA[65:42] == REMOTE_FAULT);
		// CW(8'h66): // The fault must've been cleared by data start,
		//   or data wouldn't be starting
		CW(8'h55): o_remote_fault <= (RX_DATA[65:42] == REMOTE_FAULT);
		CW(8'h4b): o_remote_fault <= (RX_DATA[33:10] == REMOTE_FAULT);
		default: o_remote_fault <= 1'b0;
		endcase

		if (RX_DATA[1:0] != SYNC_CONTROL)
			o_remote_fault <= 1'b0;

		case(RX_DATA[9:2])
		CW(8'h1e): r_local_fault <= 1'b0;
		CW(8'h2d): r_local_fault <= (RX_DATA[65:42] != REMOTE_FAULT);
		CW(8'h33): r_local_fault <= 1'b0;
		CW(8'h66): r_local_fault <= (RX_DATA[33:10] != REMOTE_FAULT);
		CW(8'h55): r_local_fault <= (RX_DATA[65:42] != REMOTE_FAULT);
		CW(8'h78): r_local_fault <= 1'b0;
		CW(8'h4b): r_local_fault <= (RX_DATA[33:10] != REMOTE_FAULT);
		CW(8'h87): r_local_fault <= past_stop;
		CW(8'h99): r_local_fault <= past_stop;
		CW(8'haa): r_local_fault <= past_stop;
		CW(8'hb4): r_local_fault <= past_stop;
		CW(8'hcc): r_local_fault <= past_stop;
		CW(8'hd2): r_local_fault <= past_stop;
		CW(8'he1): r_local_fault <= past_stop;
		CW(8'hff): r_local_fault <= past_stop;
		default: r_local_fault <= 1'b1;
		endcase

		if (1'b0 == (^RX_DATA[1:0]))
			r_local_fault <= 1'b1;
		else if (RX_DATA[1:0] != SYNC_CONTROL)
			r_local_fault <= 1'b0;
	end
	// }}}

	// watchdog_timeout
	// {{{
	// If the PHY never produces any data for us, then we have a watchdog
	// error condition.
	always @(posedge RX_CLK)
	if (!S_ARESETN)
	begin
		watchdog_counter <= -1;
		watchdog_timeout <=  0;
	end else if (RX_VALID)
	begin
		watchdog_counter <= -1;
		watchdog_timeout <=  0;
	end else begin
		if (watchdog_counter > 0)
			watchdog_counter <= watchdog_counter - 1;
		watchdog_timeout <= (watchdog_counter <= 1);
	end
	// }}}

	// max_packet_fault
	// {{{
	// It is a fault to have a continuous packet with no control characters.
	// In this case, our maximum packet length is still excessively large,
	// set (above) at 2^19 words, or 2^22 (4MB) bytes.
	always @(posedge RX_CLK)
	if (!S_ARESETN)
	begin
		max_packet_counter <= -1;
		max_packet_fault <=  0;
	end else if (RX_VALID)
	begin
		if (RX_DATA[1:0] == SYNC_CONTROL)
		begin
			max_packet_counter <= -1;
			max_packet_fault <=  0;
		end else if (max_packet_counter != 0)
		begin
			max_packet_counter <= max_packet_counter - 1;
			max_packet_fault <= (max_packet_counter <= 1);
		end
	end
`ifdef	FORMAL
	always @(*)
	if (S_ARESETN)
		assert(max_packet_fault == (max_packet_counter == 0));
	always @(posedge RX_CLK)
	if (S_ARESETN && $past(S_ARESETN && max_packet_fault
				&& RX_DATA[1:0] != SYNC_CONTROL))
		assert(max_packet_fault);
`endif
	// }}}

	// link_up_counter--used to stretch faults and errors so the eye can
	// see them
	// {{{
	always @(posedge RX_CLK or negedge S_ARESETN)
	if (!S_ARESETN)
		link_up_counter <= 0;
	else if (watchdog_timeout || o_local_fault
			|| max_packet_fault || powering_up)
		link_up_counter <= 0;
	else if (!link_up_counter[LNKMSB] || o_remote_fault)
		// Blink on remote fault, hold steady if everything is good
		link_up_counter <= link_up_counter+1;
	// }}}

	always @(posedge RX_CLK or negedge S_ARESETN)
	if (!S_ARESETN)
		powering_up <= 1'b1;
	else if (RX_VALID && !r_fault && RX_DATA[1:0] == SYNC_CONTROL)
		powering_up <= 1'b0;

	assign	o_link_up = link_up_counter[LNKMSB];

	// stretch_fault
	// {{{
	// Used to lengthen local fault signals sufficient that they can cross
	// clock domains reliably and so be used in the return signaling.
	always @(posedge RX_CLK)
	if (!S_ARESETN)
	begin
		stretch_local <= -1;
		stretch_fault <=  1;
	end else if (powering_up || r_local_fault || watchdog_timeout)
	begin
		stretch_local <= -1;
		stretch_fault <=  1;
	end else begin
		if (stretch_local > 0)
			stretch_local <= stretch_local - 1;
		stretch_fault <= (stretch_local > 1);
	end
	// }}}

	assign o_local_fault = stretch_fault || powering_up;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// M_*: The final output
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	M_VALID = 1'b0;
	always @(posedge RX_CLK)
	if (!S_ARESETN)
		M_VALID <= 0;
	else if (!M_VALID || M_READY)
		M_VALID <= dly_valid && (RX_VALID || dly_last) && !M_ABORT;

	always @(posedge RX_CLK)
	if (!M_VALID || M_READY)
	begin
		M_DATA <= dly_data;
		M_BYTES<= (dly_bytes[3] || !dly_last) ? 3'h0 : dly_bytes[2:0];
		M_LAST <= (dly_last && dly_bytes <= 8)
			|| (!poffset && RX_VALID
				&& RX_DATA[9:0] == { CW(8'h87), SYNC_CONTROL });
	end

	always @(posedge RX_CLK)
	if (!S_ARESETN)
		M_ABORT <= 1'b0;
	else if (RX_VALID && dly_valid && M_VALID && !M_READY)
		M_ABORT <= 1'b1;
	else if (r_local_fault && (M_VALID || dly_valid))
		M_ABORT <= 1'b1;
	else if (r_fault && ((dly_valid && !dly_last)
				|| (M_VALID && (!M_READY || !M_LAST))))
		M_ABORT <= 1'b1;
	else if (dly_valid && !M_ABORT)
	begin
		if (dly_last)
			M_ABORT <= 1'b0;
		else if (RX_VALID && RX_DATA[1:0] == SYNC_CONTROL)
		begin
			case(RX_DATA[9:2])
			CW(8'h87): begin end
			CW(8'h99): begin end
			CW(8'haa): begin end
			CW(8'hb4): begin end
			CW(8'hcc): begin end
			CW(8'hd2): begin end
			CW(8'he1): begin end
			CW(8'hff): begin end
			default: M_ABORT <= 1'b1;
			endcase
		end
	end else if (!M_VALID || M_READY)
		M_ABORT <= 1'b0;
	// }}}

	function automatic [7:0] CW(input [7:0] in);
		// {{{
		// This function basically performs a bit reverse.
		//
		// Our codewords arrive in a bit-reversed order.  Swap that
		// order here.  By placing this into a function, we can 1) use
		// the codewords actually listed in the IEEE specification, and
		// 2) easily swap back and forth between bit-reversed and not
		// if necessary.
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
	// Local declarations
	// {{{
	reg	f_past_valid;
	// Verilator lint_off UNDRIVEN
	(* anyseq *)	reg	fc_check_pkt;
	(* anyconst *)	reg	[17:0]	fc_posn,	// Byte position
					fc_len;		// Packet length
	(* anyconst *)	reg	[7:0]	fc_data;	// Data value @ posn
	// Verilator lint_on  UNDRIVEN
	reg	[17:0]	frx_count, frx_posn, fm_count;
	reg		frx_now, fm_now;
	reg	[65:0]	frx_byte;
	reg	[63:0]	frx_word;
	reg	[63:0]	fm_byte;
	reg		f_midpkt;
	reg	[2:0]	frx_shift;
	reg		f_preamble, f_half_preamble, f_sync_data, f_eop;
	reg	[7:0]	f_ctrl_byte;
	reg	[12:0]	fm_word;
	reg	[11:0]	fm_pkts;



	initial	f_past_valid = 0;
	always @(posedge RX_CLK)
		f_past_valid <= 1;

	always @(posedge RX_CLK)
	if (!f_past_valid)
		assume(!S_ARESETN);

	always @(posedge RX_CLK)
	if (!RX_VALID || RX_DATA[1:0] == SYNC_DATA
			|| f_preamble || f_half_preamble
			|| pstate || r_local_fault
			|| dly_valid || $past(dly_valid)
			|| M_VALID || M_ABORT)
		assume($stable(fc_check_pkt));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assume a valid incoming state
	// {{{

	always @(posedge RX_CLK)
	if (f_preamble || f_half_preamble)
		f_midpkt <= 1'b1;
	else if (f_eop)
		f_midpkt <= 1'b0;

	always @(*)
	if (S_ARESETN && !f_midpkt)
	begin
		assert(!dly_valid || dly_last);
		if (!M_VALID && !M_ABORT)
			assert(fm_word == 0);
	end

	always @(*)
	if (f_midpkt)
		assume(!f_preamble && !f_half_preamble);

	always @(*)
	if (!f_midpkt)
		assume(!f_eop);

	always @(*)
	if (RX_VALID)
	begin
		if (!f_midpkt)
		begin
			assume(RX_DATA[1:0] == SYNC_CONTROL);
		end

		case(f_ctrl_byte)
		CW(8'h1e): assume(!f_midpkt);
		CW(8'h2d): assume(!f_midpkt && RX_DATA[57:42] == 16'h0);
		CW(8'h33): assume(!f_midpkt && RX_DATA[65:42] == 24'habaaaa);
		CW(8'h66): assume(!f_midpkt && RX_DATA[65:42] == 24'habaaaa);
		CW(8'h55): assume(!f_midpkt && RX_DATA[65:50] == 16'h0 && RX_DATA[33:18] == 16'h0);
		CW(8'h78): assume(!f_midpkt);
		CW(8'h4b): assume(!f_midpkt && RX_DATA[33:18] == 16'h0);
		//
		CW(8'h87): assume( f_midpkt);
		CW(8'h99): assume( f_midpkt);
		CW(8'haa): assume( f_midpkt);
		CW(8'hb4): assume( f_midpkt);
		CW(8'hcc): assume( f_midpkt);
		CW(8'hd2): assume( f_midpkt);
		CW(8'he1): assume( f_midpkt);
		CW(8'hff): assume( f_midpkt);
		default: assume(1'b0);
		endcase
	end

	always @(posedge RX_CLK)
	if (S_ARESETN && pstate && !r_local_fault)
		assert(f_midpkt);

	always @(*)
		f_preamble = RX_VALID && RX_DATA == R_PREAMBLE;
	always @(*)
		f_half_preamble = RX_VALID && (
			((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE1)
			|| ((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE2));
	always @(*)
		f_sync_data = RX_VALID && (RX_DATA[1:0] == SYNC_DATA);
	always @(*)
		f_ctrl_byte = RX_DATA[9:2];
	always @(*)
	if (!S_ARESETN || !RX_VALID || RX_DATA[1:0] != SYNC_CONTROL)
		f_eop = 1'b0;
	else case(RX_DATA[9:2])
	CW(8'h87): f_eop = 1'b1;
	CW(8'h99): f_eop = 1'b1;
	CW(8'haa): f_eop = 1'b1;
	CW(8'hb4): f_eop = 1'b1;
	CW(8'hcc): f_eop = 1'b1;
	CW(8'hd2): f_eop = 1'b1;
	CW(8'he1): f_eop = 1'b1;
	CW(8'hff): f_eop = 1'b1;
	default: f_eop = 1'b0;
	endcase

	always @(posedge RX_CLK)
	if (fc_check_pkt && f_midpkt)
		assume(RX_VALID || $past(RX_VALID));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Count incoming data
	// {{{

	always @(*)
		assume(fc_len > 9);

	always @(posedge RX_CLK)
	if (!S_ARESETN)
		frx_count <= 0;
	else if (RX_VALID && RX_DATA == R_PREAMBLE)
		frx_count <= 8;
	else if (RX_VALID && ((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE1))
		frx_count <= 4;
	else if (RX_VALID && ((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE2))
		frx_count <= 4;
	else if (RX_VALID)
	begin
		if (RX_DATA[1:0] == SYNC_DATA)
			frx_count <= frx_count + 8;
		else if (frx_count > 0)
		case(RX_DATA[9:2])
		CW(8'h87): frx_count <= frx_count;
		CW(8'h99): frx_count <= frx_count + 1;
		CW(8'haa): frx_count <= frx_count + 2;
		CW(8'hb4): frx_count <= frx_count + 3;
		CW(8'hcc): frx_count <= frx_count + 4;
		CW(8'hd2): frx_count <= frx_count + 5;
		CW(8'he1): frx_count <= frx_count + 6;
		CW(8'hff): frx_count <= frx_count + 7;
		default: if (fc_check_pkt) assume(0);
		endcase
	end

	always @(*)
	if (S_ARESETN && f_midpkt && fc_check_pkt && pstate)
	begin
		assert(frx_count[1:0] == 2'b00);
		assert(frx_count[2] == poffset);
	end

	always @(*)
	if (S_ARESETN && RX_VALID && f_midpkt && fc_check_pkt)
	begin
		if (frx_count + 8 <= fc_len)
		begin
			assume(RX_DATA[1:0] == SYNC_DATA);
		end else case(RX_DATA[9:0])
		{ CW(8'h87), SYNC_CONTROL }: assume(frx_count == fc_len);
		{ CW(8'h99), SYNC_CONTROL }: assume(frx_count + 1 == fc_len);
		{ CW(8'haa), SYNC_CONTROL }: assume(frx_count + 2 == fc_len);
		{ CW(8'hb4), SYNC_CONTROL }: assume(frx_count + 3 == fc_len);
		{ CW(8'hcc), SYNC_CONTROL }: assume(frx_count + 4 == fc_len);
		{ CW(8'hd2), SYNC_CONTROL }: assume(frx_count + 5 == fc_len);
		{ CW(8'he1), SYNC_CONTROL }: assume(frx_count + 6 == fc_len);
		{ CW(8'hff), SYNC_CONTROL }: assume(frx_count + 7 == fc_len);
		default: begin
			assume(0);
			end
		endcase
	end

	always @(*)
	if (frx_count == 4 && RX_VALID && fc_check_pkt)
		assume(RX_DATA[33:0] == {24'hABAA_AA, CW(8'hAA), SYNC_DATA });

	always @(*)
	if (fc_check_pkt)
		assume(frx_count <= fc_len);

	always @(*)
	if (fc_check_pkt && frx_count == fc_len)
		assume(!f_midpkt);

	always @(*)
	if (fc_check_pkt && frx_count + 8 < fc_len && frx_count < fc_len)
		assume(!RX_VALID || RX_DATA[1:0] == SYNC_DATA);

	always @(*)
	if (S_ARESETN && !r_fault && !r_local_fault)
	begin
		if (dly_last)
		begin
			assert(M_VALID);
			assert(!pstate);
		end

		if (!f_midpkt && dly_valid)
			assert(dly_last);
		if (dly_last && !M_ABORT)
			assert(dly_valid || (M_VALID && M_LAST));
	end

	always @(*)
	if (S_ARESETN && dly_valid && !dly_last)
		assert(dly_bytes == 12 || dly_bytes == 8);

	always @(*)
	if (S_ARESETN && M_VALID && M_LAST)
	begin
		assert(!poffset);
		assert(!dly_valid);
		// assert(!dly_last);
		assert(dly_bytes[2:0] == 0);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing interface properties
	// {{{

	faxin_master #(
		.DATA_WIDTH(64), .MIN_LENGTH(1), .MAX_LENGTH(8191)
	) faxin (
		.S_AXI_ACLK(RX_CLK), .S_AXI_ARESETN(S_ARESETN),
		.S_AXIN_VALID(M_VALID), .S_AXIN_READY(M_READY),
		.S_AXIN_DATA(M_DATA), .S_AXIN_BYTES(M_BYTES),
		.S_AXIN_LAST(M_LAST), .S_AXIN_ABORT(M_ABORT),
		.f_stream_word(fm_word), .f_packets_rcvd(fm_pkts)
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Count outgoing data
	// {{{
	always @(posedge RX_CLK)
	if (!S_ARESETN)
		fm_count <= 0;
	else if (M_ABORT && (!M_VALID || M_READY))
		fm_count <= 0;
	else if (M_VALID && M_READY)
	begin
		if (M_LAST)
			fm_count <= 0;
		else if (M_BYTES == 0)
			fm_count <= fm_count + 8;
		else
			// Verilator lint_off WIDTH
			fm_count <= fm_count + M_BYTES;
			// Verilator lint_on  WIDTH
	end

	always @(posedge RX_CLK)
	if (S_ARESETN && !pstate && !dly_valid && !M_VALID && !M_ABORT)
		assert(fm_word == 0);

	always @(posedge RX_CLK)
	if (S_ARESETN && !M_ABORT)
		assert(fm_count == { fm_word, 3'h0 });

	// Assert that any check packet matches the correct length
	always @(posedge RX_CLK)
	if (S_ARESETN && fc_check_pkt && M_VALID)
	begin
		if (!M_LAST)
		begin
			assert(fm_count + 8 < fc_len);
		end else if (M_BYTES == 0)
		begin
			assert(fm_count + 16 == fc_len);
		end else begin
			// Verilator lint_off WIDTH
			assert(fm_count + 8 + M_BYTES == fc_len);
			// Verilator lint_on  WIDTH
		end
	end

	always @(*)
	if (fc_check_pkt && (pstate || dly_valid || M_VALID))
		assume(!f_preamble && !f_half_preamble);

	always @(*)
	if (fc_check_pkt)
		assume(!r_local_fault);

	always @(posedge RX_CLK)
	if (f_past_valid && S_ARESETN && fc_check_pkt)
		assert(!M_ABORT);

	always @(posedge RX_CLK)
	if (f_past_valid && S_ARESETN && !dly_valid
						&& !r_local_fault && !r_fault)
		assert(!M_VALID || M_LAST || M_ABORT);

	always @(posedge RX_CLK)
	if (f_past_valid && S_ARESETN && M_VALID && M_LAST)
		assert(dly_bytes[2:0] == 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assume incoming contract data
	// {{{

	always @(*)
		frx_posn = frx_count - 8;

	always @(*)
		frx_shift = fc_posn + 8 - frx_count;

	always @(*)
		frx_word = RX_DATA[65:2];

	always @(*)
	if (RX_DATA[1:0] == SYNC_CONTROL)
		frx_byte = RX_DATA[65:10] >> ({ frx_shift, 3'h0 });
	else
		frx_byte = frx_word >> ({ frx_shift, 3'h0 });

	(* keep *) reg	[1:0]	frx_check;
	(* keep *) reg	[2:0]	frx_check2;
	always @(*)
	begin
		frx_check2[0] = (frx_count < 8);
		frx_check2[1] = (frx_posn > fc_posn);
		frx_check2[2] = (fc_posn <= frx_posn + 8);
	end

	always @(*)
	if (!fc_check_pkt || !RX_VALID || frx_count < 4 || powering_up
						|| r_fault || r_local_fault)
	begin
		frx_now = 0;
		frx_check = 0;
	end else if ((frx_count < 8)
		|| (frx_posn > fc_posn) || (fc_posn >= frx_posn + 8))
	begin
	// else if (fc_posn + 8 < frx_count || fc_posn + 8 >= frx_count + 8)
		frx_now = 0;
		frx_check = 1;
	end else if (RX_DATA[1:0] == SYNC_DATA)
	begin
		frx_now = 1;
		frx_check = 2;
	end else begin
		frx_check = 3;
		case(f_ctrl_byte)
	CW(8'h99): frx_now = (fc_posn < frx_posn + 1);
	CW(8'haa): frx_now = (fc_posn < frx_posn + 2);
	CW(8'hb4): frx_now = (fc_posn < frx_posn + 3);
	CW(8'hcc): frx_now = (fc_posn < frx_posn + 4);
	CW(8'hd2): frx_now = (fc_posn < frx_posn + 5);
	CW(8'he1): frx_now = (fc_posn < frx_posn + 6);
	CW(8'hff): frx_now = (fc_posn < frx_posn + 7);
	default: begin end
	endcase
	end

	always @(posedge RX_CLK)
	if (S_ARESETN && frx_now && fc_check_pkt)
		assume(frx_byte[7:0] == fc_data);

	always @(*)
	if (fc_check_pkt)
	begin
		assume(!i_phy_fault);
		assume(!r_local_fault);
		assume(watchdog_counter > 100);
		assume({ r_fault, r_fault_pipe } == 0);
	end

	always @(*)
	if (S_ARESETN && frx_count >= 8 && pstate && !M_ABORT)
	begin
		if (!dly_last)
		assert(frx_count == fm_count + (dly_valid ? dly_bytes : 0) + 8 + (M_VALID ? 8:0));
		assert(frx_count[2] == poffset);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assert outgoing contract data
	// {{{
	always @(*)
	if (!S_ARESETN || !M_VALID || M_ABORT || !fc_check_pkt
			|| fm_count > fc_posn || fm_count + 8 <= fc_posn)
		fm_now = 0;
	// Verilator lint_off WIDTH
	else if (M_BYTES == 0 || fc_posn < fm_count + M_BYTES)
	// Verilator lint_on  WIDTH
		fm_now = 1;
	else
		fm_now = 0;

	always @(*)
		fm_byte = M_DATA >> (8*(fc_posn - fm_count));

	always @(posedge RX_CLK)
	if (fm_now)
		assert(fm_byte[7:0] == fc_data);
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{

	// always @(*) assume(!poffset);

	always @(posedge RX_CLK)
	if ($past(f_preamble || f_half_preamble)
			|| (!$past(RX_VALID) && $past(f_preamble||f_half_preamble, 2)))
		assume(!f_eop);

	always @(posedge RX_CLK)
	if (f_midpkt)
		assume(RX_VALID || $past(RX_VALID));

	always @(*)
	if (fc_check_pkt)
		assume(!M_VALID || M_READY ||M_LAST);

always @(*)
	assume(fm_word < 8190);

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, fm_byte[63:8], frx_byte[65:8] };
	// Verilator lint_on  UNUSED
	// }}}
`endif
// }}}
endmodule
