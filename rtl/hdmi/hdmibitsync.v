////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/hdmibitsync.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	
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
module	hdmibitsync (
		// {{{
		input	wire		i_pix_clk, i_reset,
		//
		input	wire	[9:0]	i_r, i_g, i_b,
		output	reg	[9:0]	o_r, o_g, o_b,
		//
		output	wire	[31:0]	o_sync_word,
		output	wire	[31:0]	o_debug
		// }}}
	);

	// Register/net declarations
	// {{{
	wire	[9:0]	auto_r,   auto_g,   auto_b;
	wire	[4:0]	auto_bitslip_r, auto_bitslip_g, auto_bitslip_b;
	reg		all_locked;
	// }}}

	// Automatically synchronize to each color stream.
	// {{{
	wire	[31:0]	dbg_red, dbg_grn, dbg_blu;

	// It is possible that we'll lock up to one color on one word and
	// another word on another cut.  Hence, we may still need to lock
	// the words together afterwards.
	hdmipixelsync
	rasync(
		.i_clk(i_pix_clk), .i_reset(i_reset),
		.i_px(i_r),
		.o_sync(auto_bitslip_r), .o_pix(auto_r),
		.o_debug(dbg_red)
	);

	hdmipixelsync
	gasync(
		.i_clk(i_pix_clk), .i_reset(i_reset),
		.i_px(i_g),
		.o_sync(auto_bitslip_g), .o_pix(auto_g),
		.o_debug(dbg_grn)
	);

	hdmipixelsync
	basync(
		.i_clk(i_pix_clk), .i_reset(i_reset),
		.i_px(i_b),
		.o_sync(auto_bitslip_b), .o_pix(auto_b),
		.o_debug(dbg_blu)
	);

	assign	o_debug = dbg_grn;
	// }}}

	// all_locked
	// {{{
	// True if all channels are locked.
	initial	all_locked = 0;
	always @(posedge i_pix_clk)
		all_locked <= auto_bitslip_r[4]
				&& auto_bitslip_g[4] && auto_bitslip_b[4];
	// }}}

	// o_r, o_g, o_b --- our bit-synchronized output channels
	// {{{
	always @(*)
	begin
		o_r = auto_r;
		o_g = auto_g;
		o_b = auto_b;
	end
	// }}}

	// o_sync_word
	// {{{
	// For reporting on the control bus: are we locked?  And if so, how?
	assign	o_sync_word = { 7'h0, !all_locked,
				3'h0, auto_bitslip_r,
				3'h0, auto_bitslip_g,
				3'h0, auto_bitslip_b };
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, dbg_red, dbg_grn, dbg_blu };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
