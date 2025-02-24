////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/xhdmiin.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A wrapper for the 1:10 ISERDES+IOBUF capability required to
//		support HDMI ingestion.
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
//
`default_nettype	none
// }}}
module	xhdmiin #(
		parameter	DC = 0
	) (
		// {{{
		input	wire		i_clk,		// Pixel clock
					i_hsclk,	// 10x pixel clock
					i_reset_n,
		input	wire	[4:0]	i_delay,
		output	wire	[4:0]	o_delay,
		input	wire	[1:0]	i_hs_wire,
		output	wire	[9:0]	o_word
		// }}}
	);

	// Local declarations
	// {{{
	wire		w_ignored;
	wire	[9:0]	w_word;

	wire	w_hs_wire, w_hs_delayed_wire;
	// }}}

	// Convert from differential to internal
	// {{{
	IBUFDS
	hdmibuf(
		.I(i_hs_wire[1]), .IB(i_hs_wire[0]),
		.O(w_hs_wire)
	);
	// }}}

	// Now separate us into the various bits
	// {{{
	xhdmiin_deserdes
	the_deserdes(
		.i_clk(i_clk),
		.i_hsclk(i_hsclk),
		.i_reset_n(i_reset_n),
		.i_delay(i_delay),
		.o_delay(o_delay),
		.i_pin(w_hs_wire),
		.o_wire(w_ignored),
		.o_word(o_word)		// Decoded data to send to 10B/8B decode
	);
	// }}}
endmodule
