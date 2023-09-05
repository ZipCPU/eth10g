////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxin_slave.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Describes the (AXI-stream like) network protocol.  This is
//		subtly different from AXI stream by the addition of an ABORT
//	signal.  If abort is ever raised, the packet is aborted and the next
//	beat will start a new packet.  This allows a source with limited
//	buffering ability to abort a packet if READY is held low.  Likewise,
//	a source that detects a CRC error can abort the last value of the packet
//	and therefore abort the whole packet if desired.
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
module	faxin_slave #(
		// {{{
		parameter	DATA_WIDTH = 32,
		parameter	MIN_LENGTH = 64*8/DATA_WIDTH,	// 64 Bytes
		parameter	MAX_LENGTH = 1024,
		// WBITS := BYTE WIDTH, number of bits necessary to specify
		// how many bytes are in use.  Must be at least $clog2(DW/8)
		parameter	WBITS = (DATA_WIDTH <= 8) ? 1
						: $clog2(DATA_WIDTH/8),
		parameter	LGMX= (MAX_LENGTH > 0) ? $clog2(MAX_LENGTH+1):1,
		localparam	DW = DATA_WIDTH
		// }}}
	) (
		// {{{
		input	wire			S_AXI_ACLK, S_AXI_ARESETN,
		//
		input	wire			S_AXIN_VALID,
						S_AXIN_READY,
		input	wire	[DW-1:0]	S_AXIN_DATA,
		input	wire [WBITS-1:0]	S_AXIN_BYTES,
		input	wire			S_AXIN_LAST,
		input	wire			S_AXIN_ABORT,
		//
		output	reg	[LGMX-1:0]	f_stream_word,
		output	reg	[12-1:0]	f_packets_rcvd
		// }}}
	);

`define	SLAVE_ASSUME	assume
`define	SLAVE_ASSERT	assert

	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	// Stream properties: VALID, DATA, LAST, ABORT, etc.
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
	begin
		`SLAVE_ASSUME(!S_AXIN_VALID);
	end else if ($past(S_AXIN_VALID && !S_AXIN_READY))
	begin
		// Stream was stalled last cycle, must remain in valid state
		// {{{
		`SLAVE_ASSUME(S_AXIN_VALID);

		if ($past(S_AXIN_ABORT))
		begin
			// If in middle of abort, DATA && LAST can both change
			`SLAVE_ASSUME(S_AXIN_ABORT);
		end else if (!S_AXIN_ABORT)
		begin
			`SLAVE_ASSUME($stable(S_AXIN_DATA));
			`SLAVE_ASSUME($stable(S_AXIN_LAST));
		end
		// }}}
	end /* else if ($past(S_AXIN_ABORT && !S_AXIN_VALID))
	begin
		// ABORT may take place mid-packet, even when no packet
		// is ready.  If so, ABORT should stay asserted until the
		// next valid which will start the next packet.
		if (!S_AXIN_VALID)
			`SLAVE_ASSUME(S_AXIN_ABORT);
	end */
	// }}}

	// Byte properties
	generate if (DW <= 8)
	begin : CHK_ONE_BYTE

		always @(*)
		if (S_AXI_ARESETN && S_AXIN_VALID)
			`SLAVE_ASSUME(S_AXIN_BYTES == 1);

	end else if (WBITS <= $clog2(DW/8))
	begin : CHK_SHORT_BYTES
		always @(*)
		if (S_AXI_ARESETN && S_AXIN_VALID && !S_AXIN_LAST)
		begin
			// The MSB is assumed, so if !S_AXIN_LAST, then
			// S_AXIN_BYTES == (DW/8), which doesn't fit in
			// $clog2(DW/8) bits.  However, when S_AXIN_LAST,
			// the number of bytes could be anything.
			`SLAVE_ASSUME(S_AXIN_BYTES == 0);
		end
	end else begin : CHK_FULL_BYTES
		always @(*)
		if (S_AXI_ARESETN && S_AXIN_VALID)
		begin
			// Here we have enough bits to fully specify
			// S_AXIN_BYTES, even though the MSB is really
			// redundant.  The rule here is that if S_AXIN_VALID
			// is ever true, there must be between 1 and DW/8
			// bytes--never zero bytes 'cause then S_AXIN_VALID
			// would've been low.
			`SLAVE_ASSUME(S_AXIN_BYTES > 0);
			`SLAVE_ASSUME(S_AXIN_BYTES <= DW/8);

			// On all but the last beat, the number of bytes must
			// be a whole word.  On the last beat, it can be less.
			if (!S_AXIN_LAST)
				`SLAVE_ASSUME(S_AXIN_BYTES == DW/8);
		end
	end endgenerate

	// f_stream_word -- measuring packet length
	// {{{
	initial	f_stream_word = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || S_AXIN_ABORT)
		f_stream_word <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
	begin
		f_stream_word <= f_stream_word + 1;
		if (S_AXIN_LAST)
			f_stream_word <= 0;
	end

	always @(*)
	if (S_AXI_ARESETN && S_AXIN_VALID && S_AXIN_LAST && !S_AXIN_ABORT)
		`SLAVE_ASSUME(MIN_LENGTH <= 1 || f_stream_word+1 >= MIN_LENGTH);

	generate if (MAX_LENGTH > 0)
	begin : F_CHECK_MAXLEN
		always @(*)
		if (S_AXI_ARESETN && !S_AXIN_ABORT)
		begin
			if (f_stream_word + 1 == MAX_LENGTH)
			begin
				`SLAVE_ASSUME(!S_AXIN_VALID || S_AXIN_LAST);
			end

			assert(f_stream_word < MAX_LENGTH);
		end
	end endgenerate
	// }}}

	// f_packets_rcvd -- counting packets received
	// {{{
	initial	f_packets_rcvd = 0;
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		f_packets_rcvd <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST && !S_AXIN_ABORT)
		f_packets_rcvd <= f_packets_rcvd + 1;
	// }}}

endmodule
`undef	SLAVE_ASSUME
`undef	SLAVE_ASSERT
