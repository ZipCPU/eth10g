////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/netstats.v
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
// Copyright (C) 2025, Gisselquist Technology, LLC
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
`default_nettype none
// }}}
module	netstats #(
		localparam	NETH = 4
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[6:0]		i_wb_addr,
		input	wire	[31:0]		i_wb_data,
		input	wire	[3:0]		i_wb_sel,
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	reg	[31:0]		o_wb_data,
		//
		input	wire	[NETH*32-1:0]	i_data
		// }}}
	);

	genvar			gk;
	wire	[NETH-1:0]	w_ack;
	wire	[NETH*32-1:0]	w_data;
	reg	[31:0]		pre_data;

	generate for (gk=0; gk<NETH; gk=gk+1)
	begin : CHANNEL_STAT
		wire	stb;
		// Verilator lint_off UNUSED
		wire	ign_stall;
		// Verilator lint_on  UNUSED

		assign	stb = i_wb_stb && i_wb_addr[6:5] == gk[1:0];

		pktstats
		u_pktstats (
			.i_clk(i_clk), .i_reset(i_reset),
			.i_wb_cyc(i_wb_cyc), .i_wb_stb(stb), .i_wb_we(i_wb_we),
			.i_wb_addr(i_wb_addr[4:0]), .i_wb_data(i_wb_data),
				.i_wb_sel(i_wb_sel),
			.o_wb_stall(ign_stall), .o_wb_ack(w_ack[gk]),
				.o_wb_data(w_data[gk*32 +: 32]),
			//
			.i_valid(i_data[32*gk+31]), .i_data(i_data[32*gk +: 31])
		);
	end endgenerate

	assign	o_wb_stall = 1'b0;

	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		o_wb_ack <= 0;
	else
		o_wb_ack <= |w_ack;

	// o_wb_data
	// {{{
	always @(*)
	begin
		pre_data = 0;
		if (w_ack[0]) pre_data = pre_data | w_data[0*32 +: 32];
		if (w_ack[1]) pre_data = pre_data | w_data[1*32 +: 32];
		if (w_ack[2]) pre_data = pre_data | w_data[2*32 +: 32];
		if (w_ack[3]) pre_data = pre_data | w_data[3*32 +: 32];
	end

	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		o_wb_data <= 0;
	else
		o_wb_data <= pre_data;
	// }}}
endmodule
