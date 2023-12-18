////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	netled
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Produce an LED sequence onto the Ethernet 10Gb LEDs which can
//		be used to demonstrate that the LEDs work as desired.  This
//	is scaffolding IP, and will be tossed rather than used in operation.
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
`timescale		1ns/1ps
`default_nettype	none
// }}}
module	netled #(
		parameter	NLINKS=4
	) (
		input	wire	i_clk,
		output	reg	[NLINKS-1:0]	o_linkup,
		output	reg	[NLINKS-1:0]	o_activity
	);

	reg		r_pps;
	reg	[39:0]	rtl_counter;
	reg	[6:0]	s_counter;

	initial	rtl_counter = 0;
	always @(posedge i_clk)
		{ r_pps, rtl_counter } <= rtl_counter + 40'd10_995;

	always @(posedge i_clk)
	if (r_pps)
		{ s_counter } <= s_counter + 1;


	always @(posedge i_clk)
	case(s_counter[6:4])
	3'h0: begin
		o_linkup[0] <= s_counter[2:0] == 3'h0;
		o_linkup[1] <= s_counter[2:0] == 3'h1;
		o_linkup[2] <= s_counter[2:0] == 3'h2;
		o_linkup[3] <= s_counter[2:0] == 3'h3;

		o_activity <= 4'h0;
		end
	3'h1: begin
		o_linkup <= 4'h0;

		o_activity[0] <= s_counter[2:0] == 3'h0;
		o_activity[1] <= s_counter[2:0] == 3'h1;
		o_activity[2] <= s_counter[2:0] == 3'h2;
		o_activity[3] <= s_counter[2:0] == 3'h3;
		end
	3'h2: begin
		o_linkup[0] <= s_counter[2:0] == 3'h0;
		o_linkup[1] <= s_counter[2:0] == 3'h1;
		o_linkup[2] <= s_counter[2:0] == 3'h2;
		o_linkup[3] <= s_counter[2:0] == 3'h3;

		o_activity[0] <= s_counter[2:0] == 3'h0;
		o_activity[1] <= s_counter[2:0] == 3'h1;
		o_activity[2] <= s_counter[2:0] == 3'h2;
		o_activity[3] <= s_counter[2:0] == 3'h3;
		end
	3'h3: begin
		o_linkup[0] <= rtl_counter[37];
		o_linkup[1] <= rtl_counter[37];
		o_linkup[2] <= rtl_counter[37];
		o_linkup[3] <= rtl_counter[37];

		o_activity[0] <= rtl_counter[37] ^ s_counter[3];
		o_activity[1] <= rtl_counter[37] ^ s_counter[3];
		o_activity[2] <= rtl_counter[37] ^ s_counter[3];
		o_activity[3] <= rtl_counter[37] ^ s_counter[3];
		end
	3'h4: begin
		o_linkup[0] <= rtl_counter[38];
		o_linkup[1] <= rtl_counter[38];
		o_linkup[2] <= rtl_counter[38];
		o_linkup[3] <= rtl_counter[38];

		o_activity[0] <= rtl_counter[38] ^ s_counter[3];
		o_activity[1] <= rtl_counter[38] ^ s_counter[3];
		o_activity[2] <= rtl_counter[38] ^ s_counter[3];
		o_activity[3] <= rtl_counter[38] ^ s_counter[3];
		end
	3'h5: begin
		o_linkup[0] <= rtl_counter[39];
		o_linkup[1] <= rtl_counter[39];
		o_linkup[2] <= rtl_counter[39];
		o_linkup[3] <= rtl_counter[39];

		o_activity[0] <= rtl_counter[39] ^ s_counter[3];
		o_activity[1] <= rtl_counter[39] ^ s_counter[3];
		o_activity[2] <= rtl_counter[39] ^ s_counter[3];
		o_activity[3] <= rtl_counter[39] ^ s_counter[3];
		end
	3'h6: begin
		case({ s_counter[2:0], rtl_counter[39:38] })
		5'h00: { o_linkup, o_activity } <= { 4'h1, 4'h0 };
		5'h01: { o_linkup, o_activity } <= { 4'h2, 4'h1 };
		5'h02: { o_linkup, o_activity } <= { 4'h4, 4'h2 };
		5'h03: { o_linkup, o_activity } <= { 4'h8, 4'h4 };
		5'h04: { o_linkup, o_activity } <= { 4'h4, 4'h8 };
		5'h05: { o_linkup, o_activity } <= { 4'h2, 4'h4 };
		5'h06: { o_linkup, o_activity } <= { 4'h1, 4'h2 };
		5'h07: { o_linkup, o_activity } <= { 4'h0, 4'h1 };
		//
		5'h08: { o_linkup, o_activity } <= { 4'h1, 4'h0 };
		5'h09: { o_linkup, o_activity } <= { 4'h2, 4'h0 };
		5'h0a: { o_linkup, o_activity } <= { 4'h4, 4'h1 };
		5'h0b: { o_linkup, o_activity } <= { 4'h8, 4'h2 };
		5'h0c: { o_linkup, o_activity } <= { 4'h4, 4'h4 };
		5'h0d: { o_linkup, o_activity } <= { 4'h2, 4'h8 };
		5'h0e: { o_linkup, o_activity } <= { 4'h1, 4'h4 };
		5'h0f: { o_linkup, o_activity } <= { 4'h0, 4'h2 };
		//
		5'h10: { o_linkup, o_activity } <= { 4'h1, 4'h0 };
		5'h11: { o_linkup, o_activity } <= { 4'h2, 4'h0 };
		5'h12: { o_linkup, o_activity } <= { 4'h4, 4'h0 };
		5'h13: { o_linkup, o_activity } <= { 4'h8, 4'h0 };
		5'h14: { o_linkup, o_activity } <= { 4'h8, 4'h1 };
		5'h15: { o_linkup, o_activity } <= { 4'h8, 4'h2 };
		5'h16: { o_linkup, o_activity } <= { 4'h8, 4'h4 };
		5'h17: { o_linkup, o_activity } <= { 4'h8, 4'h8 };
		//
		5'h18: { o_linkup, o_activity } <= { 4'h8, 4'h4 };
		5'h19: { o_linkup, o_activity } <= { 4'h8, 4'h2 };
		5'h1a: { o_linkup, o_activity } <= { 4'h8, 4'h1 };
		5'h1b: { o_linkup, o_activity } <= { 4'h8, 4'h0 };
		5'h1c: { o_linkup, o_activity } <= { 4'h4, 4'h0 };
		5'h1d: { o_linkup, o_activity } <= { 4'h2, 4'h0 };
		5'h1e: { o_linkup, o_activity } <= { 4'h1, 4'h0 };
		5'h1f: { o_linkup, o_activity } <= { 4'h0, 4'h0 };
		//
		endcase end
	default: begin
		o_linkup <= 0;
		o_activity <= 0;
		end
	endcase

endmodule
