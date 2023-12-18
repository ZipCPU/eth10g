////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	netskid.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	An abortable skid buffer, using our network protocol.
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
`default_nettype	none
// }}}
module	netskid #(
		parameter	DW = 32
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			S_AXIN_VALID,
		output	wire			S_AXIN_READY,
		input	wire	[DW-1:0]	S_AXIN_DATA,
		input	wire			S_AXIN_LAST,
		input	wire			S_AXIN_ABORT,
		//
		output	reg			M_AXIN_VALID,
		input	wire			M_AXIN_READY,
		output	reg	[DW-1:0]	M_AXIN_DATA,
		output	reg			M_AXIN_LAST,
		output	reg			M_AXIN_ABORT
		// }}}
	);

	// Local declarations
	// {{{
	reg			r_valid, r_last, r_abort;
	reg	[DW-1:0]	r_data;
	// }}}

	// r_valid
	// {{{
	initial	r_valid = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_valid <= 0;
	else
		r_valid <= M_AXIN_VALID && !M_AXIN_READY;
	// }}}

	// r_data, r_last
	// {{{
	always @(posedge i_clk)
	if (S_AXIN_READY)
		{ r_data, r_last } <= { S_AXIN_DATA, S_AXIN_LAST };
	// }}}

	// r_abort
	// {{{
	initial	r_abort = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_abort <= 0;
	else if (M_AXIN_VALID && !M_AXIN_READY)
		// If we are stalled
		r_abort <= M_AXIN_ABORT;
	else if (M_AXIN_READY)
		r_abort <= 0;
	// }}}

	assign	S_AXIN_READY = !r_valid;

	// M_AXIN_*
	// {{{
	always @(*)
	begin
		if (r_valid)
		begin
			M_AXIN_VALID = 1'b1;
			M_AXIN_DATA  = r_data;
			M_AXIN_LAST  = r_last;

			M_AXIN_ABORT = r_abort || (!r_last && S_AXIN_ABORT);
		end else begin
			M_AXIN_VALID = S_AXIN_VALID;
			M_AXIN_DATA  = S_AXIN_DATA;
			M_AXIN_LAST  = S_AXIN_LAST;
			M_AXIN_ABORT = S_AXIN_ABORT;
		end

	/*
		if (i_reset)
		begin
			M_AXIN_VALID = 1'b0;
			M_AXIN_ABORT = 1'b0;
		end
	*/
	end
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
	wire	[10:0]	fslv_word, fmst_word;
	wire	[11:0]	fslv_packets, fmst_packets;
	(* anyconst *)	reg	[DW:0]	f_never_data_last;
	(* anyconst *)	reg		fnvr_abort;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	faxin_slave #(
		.DATA_WIDTH(DW)
	) fslv (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(S_AXIN_VALID),
		.S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA( S_AXIN_DATA),
		.S_AXIN_BYTES(0),
		.S_AXIN_LAST( S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		//
		.f_stream_word(fslv_word),
		.f_packets_rcvd(fslv_packets)
		// }}}
	);

	faxin_master #(
		.DATA_WIDTH(DW)
	) fmst (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(M_AXIN_VALID),
		.S_AXIN_READY(M_AXIN_READY),
		.S_AXIN_DATA( M_AXIN_DATA),
		.S_AXIN_BYTES(0),
		.S_AXIN_LAST( M_AXIN_LAST),
		.S_AXIN_ABORT(M_AXIN_ABORT),
		//
		.f_stream_word(fmst_word),
		.f_packets_rcvd(fmst_packets)
		// }}}
	);

	always @(*)
	if (!i_reset)
	begin
		if ((r_valid && r_last) || r_abort)
		begin
			assert(fslv_word == 0);
		end else
			assert(fslv_word == fmst_word + r_valid);

		if (!r_valid)
			assert(!r_abort);
	end

	always @(*)
	if (!i_reset)
	begin
		assume(!fslv_packets[11]);
		assert(fslv_packets == fmst_packets
				+ ((r_valid && r_last && !r_abort) ? 1:0));
	end

	always @(*)
	if (S_AXIN_VALID)
		assume({ S_AXIN_LAST, S_AXIN_DATA } != f_never_data_last);

	always @(*)
	if (f_past_valid && M_AXIN_VALID)
		assert({ M_AXIN_LAST, M_AXIN_DATA } != f_never_data_last);

	always @(*)
	if (fnvr_abort)
		assume(!S_AXIN_ABORT);

	always @(*)
	if (!i_reset && fnvr_abort)
		assert(!M_AXIN_ABORT);

`endif
// }}}
endmodule
