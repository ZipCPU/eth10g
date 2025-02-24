////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/txgetports.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Stall an incoming packet stream long enough to request a
//		MAC port lookup, then forward the packet to the port
//	returned, or broadcast it to all if no port was found (i.e. the
//	port bit mask returned).
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2025, Gisselquist Technology, LLC
// {{{
// This file is part of the ETH10G project.
//
// The ETH10G project contains free software and gateware, licensed under the
// terms of the 3rd version of the GNU General Public License as published by
// the Free Software Foundation.
//
// This project is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module txgetports #(
		// {{{
		parameter [0:0]	OPT_SKIDBUFFER   = 1'b0,
		parameter [0:0]	OPT_LOWPOWER     = 1'b0,
		parameter [0:0]	OPT_LITTLE_ENDIAN= 1'b0,
		// parameter [0:0]	OPT_DEFBROADCAST = 1'b0
		// parameter [0:0]	OPT_ONE_TO_MANY  = 1'b0
		parameter	NETH = 4,	// Total number of ports
		parameter	DW = 128,	// Bits per beat
		parameter	WBITS = $clog2(DW/8),	// Bits for bytes/beat
		parameter	MACW = 48	// Bits in a MAC address
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Incoming packet header data from all interfaces
		// {{{
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[DW-1:0]	S_DATA,
		input	wire [WBITS-1:0]	S_BYTES,
		input	wire			S_LAST,
		input	wire			S_ABORT,	// == 0 on TX
		// }}}
		// Table lookup interface
		// {{{
		output	reg				TBL_REQUEST,
		input	wire				TBL_VALID,
		output	wire	[MACW-1:0]		TBL_MAC,
		input	wire	[NETH-1:0]		TBL_PORT,
		// }}}
		// Outgoing packet data, following destination lookup
		// {{{
		output	reg				M_VALID,
		input	wire				M_READY,
		output	reg	[DW-1:0]		M_DATA,
		output	reg	[WBITS-1:0]		M_BYTES,
		output	reg				M_LAST,
		output	reg				M_ABORT,
		output	reg	[NETH-1:0]		M_PORT
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg			known_ports;
	wire			skd_valid, skd_ready;
	wire	[DW-1:0]	skd_data;
	wire	[WBITS-1:0]	skd_bytes;
	wire			skd_last, skd_abort;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) skidbuffer
	// {{{

	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER

		netskid #(
			.DW(WBITS+DW)
		) u_skidbuffer (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.S_AXIN_VALID(S_VALID), .S_AXIN_READY(S_READY),
			.S_AXIN_DATA({ S_BYTES, S_DATA }),
			.S_AXIN_LAST(S_LAST), .S_AXIN_ABORT(S_ABORT),
			//
			.M_AXIN_VALID(skd_valid), .M_AXIN_READY(skd_ready),
			.M_AXIN_DATA({ skd_bytes, skd_data }),
			.M_AXIN_LAST(skd_last), .M_AXIN_ABORT(skd_abort)
			// }}}
		);

	end else begin : NO_SKIDBUFFER
		assign	skd_valid = S_VALID;
		assign	S_READY   = skd_ready;
		assign	skd_data  = S_DATA;
		assign	skd_bytes = S_BYTES;
		assign	skd_last  = S_LAST;
		assign	skd_abort = S_ABORT;
	end endgenerate

	assign	skd_ready = (!M_VALID || M_READY) && known_ports;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Extract the port
	// {{{

	// assert(MACW < DW)

	always @(posedge i_clk)
	if (i_reset)
		known_ports <= 1'b0;
	else if (!known_ports && skd_valid && TBL_REQUEST && TBL_VALID)
		known_ports <= 1'b1;
	else if (skd_abort && (!skd_valid || skd_ready))
		known_ports <= 1'b0;
	else if (skd_valid && skd_ready && skd_last)
		known_ports <= 1'b0;

	initial	M_PORT = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		M_PORT <= 0;
	else if (TBL_REQUEST && TBL_VALID && (!OPT_LOWPOWER || !skd_abort))
		M_PORT <= TBL_PORT;
	else if (OPT_LOWPOWER && ((M_VALID && M_READY && M_LAST)
				|| (M_ABORT && (!M_VALID || M_READY))))
		M_PORT <= 0;

	initial	TBL_REQUEST = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		TBL_REQUEST <= 1'b0;
	else if (TBL_REQUEST)
		TBL_REQUEST <= !TBL_VALID;
	else
		TBL_REQUEST <= !M_VALID && skd_valid && !known_ports;

	// WARNING: This requires at least 48*2 bits per beat, so a minimum
	// of 128 bits per beat once rounded to a power of two
	generate if (OPT_LITTLE_ENDIAN)
	begin : GEN_LILMAC
		// The first MACW bits are the destination
		assign	TBL_MAC = skd_data[0 +: MACW];
	end else begin : GEN_BIGMAC
		// Same thing, but the "first" bits are in the MSBs
		assign	TBL_MAC = skd_data[DW-MACW +: MACW];
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate our output port
	// {{{
	initial	M_VALID = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		M_VALID <= 1'b0;
	else if (skd_valid && known_ports && !skd_abort)
		M_VALID <= 1'b1;
	else if (M_READY)
		M_VALID <= 1'b0;

	initial	{ M_LAST, M_BYTES, M_DATA } = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		{ M_LAST, M_BYTES, M_DATA } <= 0;
	else if (!M_VALID || M_READY)
	begin
		{ M_LAST, M_BYTES, M_DATA }<= { skd_last, skd_bytes, skd_data };
		if (OPT_LOWPOWER && (!skd_valid || !known_ports || skd_abort))
			{ M_LAST, M_BYTES, M_DATA } <= 0;
	end

	always @(posedge i_clk)
	if (i_reset)
		M_ABORT <= 0;
	else if (M_VALID && !M_READY && M_LAST && !M_ABORT)
		M_ABORT <= 0;
	else if (skd_abort)
		M_ABORT <= 1'b1;
	else if (!M_VALID || M_READY)
		M_ABORT <= 1'b0;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
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
	localparam	LGMX = 11;
	wire	[LGMX-1:0]	fslv_word, fmst_word;
	wire	[12-1:0]	fslv_packets, fmst_packets;
	reg			f_tbl_valid, f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	faxin_slave #(
		.MAX_LENGTH(1<<(LGMX-1)),
		.DATA_WIDTH(DW)
	) fslv (
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(S_VALID),
		.S_AXIN_READY(S_READY),
		.S_AXIN_DATA(S_DATA),
		.S_AXIN_BYTES(S_BYTES),
		.S_AXIN_LAST(S_LAST),
		.S_AXIN_ABORT(S_ABORT),
		//
		.f_stream_word(fslv_word),
		.f_packets_rcvd(fslv_packets)
	);

	faxin_master #(
		.MAX_LENGTH(1<<(LGMX-1)),
		.DATA_WIDTH(DW)
	) fmst (
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(M_VALID),
		.S_AXIN_READY(M_READY),
		.S_AXIN_DATA(M_DATA),
		.S_AXIN_BYTES(M_BYTES),
		.S_AXIN_LAST(M_LAST),
		.S_AXIN_ABORT(M_ABORT),
		//
		.f_stream_word(fmst_word),
		.f_packets_rcvd(fmst_packets)
	);

	initial	f_tbl_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		f_tbl_valid <= 1'b0;
	else
		f_tbl_valid <= TBL_REQUEST && !TBL_VALID;

	always @(*)
		assume(f_tbl_valid == TBL_VALID);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && $past(TBL_REQUEST && !TBL_VALID)
		&& !skd_abort)
	begin
		assert(TBL_REQUEST);
		assert($stable(TBL_MAC));
	end

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && $past(M_VALID && !M_READY))
	begin
		assert($stable(M_PORT));
	end

	always @(*)
	if (f_past_valid && known_ports)
		assert(!TBL_REQUEST);

	always @(*)
	if (f_past_valid && !TBL_REQUEST)
		assert(!TBL_VALID);

	always @(*)
	if (f_past_valid && !M_ABORT && (M_VALID || fmst_word > 0))
		assert(known_ports || (M_VALID && M_LAST));

	always @(posedge i_clk)
	if (!i_reset)
	begin
		if (TBL_REQUEST)
			assert(fslv_word == 0);
		if ((!M_VALID || !M_LAST) && !M_ABORT)
			assert(fslv_word == fmst_word + (M_VALID ? 1:0));

		if ((M_VALID && M_LAST) || M_ABORT)
			assert(fslv_word == 0);

		if (fslv_word > 0)
			assert(known_ports);

		if (fmst_word > 0)
			assert($stable(M_PORT));

		if (fslv_word == 0)
			assert(!M_VALID || M_LAST || M_ABORT);

		assume(!fslv_packets[11]);
		assert(fslv_packets == fmst_packets
			+ ((M_VALID && M_LAST && !M_ABORT) ? 1:0));
	end

	(* anyconst *) reg	[NETH-1:0]	fnvr_port;

	always @(*)
	if (TBL_VALID)
		assume(TBL_PORT != fnvr_port);

	always @(*)
	if (!i_reset && !skd_abort && (fslv_word > 0))
		assert(known_ports);

	always @(*)
	if (!i_reset && !skd_abort && (fslv_word == 0))
		assert(!known_ports || (!M_VALID && skd_valid && skd_ready));

	always @(*)
	if (!i_reset && known_ports)
		assert((skd_valid && skd_ready) || M_VALID || fmst_word > 0);

	always @(*)
	if (!i_reset && (M_VALID || fmst_word > 0))
		assert(M_PORT != fnvr_port);
	////////////////////////////////////////////////////////////////////////
	//
	// Lowpower properties
	// {{{
	always @(*)
	if (OPT_LOWPOWER && !M_VALID)
	begin
		assert(M_DATA  == 0);
		assert(M_BYTES == 0);
		assert(M_LAST  == 0);
	end

	always @(posedge i_clk)
	if (f_past_valid && OPT_LOWPOWER && !M_VALID && fmst_word == 0 && !known_ports)
		assert(M_PORT == 0 || $past(known_ports));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{

	always @(posedge i_clk)
		cover(!i_reset && $past(!i_reset && M_VALID && M_READY && M_LAST));
	// }}}
`endif
// }}}
endmodule
