////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xhdmiout.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Encapsulates Xilinx's 7-series 10:1 OSERDES element in a fashion
//		that works nicely with the rest of my HDMI infrastructure.
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
//
`default_nettype	none
// `define	BYPASS_SERDES
//
// }}}
module	xhdmiout (
		// {{{
		input	wire		i_clk,
		input	wire		i_hsclk,
		input	wire		i_reset_n,
		input	wire	[9:0]	i_word,
		output	wire	[1:0]	o_port
		// }}}
	);

	// Local declarations
	// {{{
	wire	[5:0]	ignored_data;
	wire	[1:0]	slave_to_master;

	(* ASYNC_REG="TRUE" *) reg		sync_reset_n;
	(* ASYNC_REG="TRUE" *) reg	[1:0]	reset_pipe;

	wire	[9:0]	w_word;
	wire	[9:0]	w_in_word;
	wire		w_hs_wire;

	// }}}

	// Generate a synchronous reset and CE signals
	// {{{
	always @(posedge i_clk or negedge i_reset_n)
	if (!i_reset_n)
		{ sync_reset_n, reset_pipe} <= 1'b0;
	else
		{ sync_reset_n, reset_pipe} <= { reset_pipe, 1'b1 };
	// }}}

	// (Optionally) bit reverse the input (not necessary)
	// {{{
	localparam	[0:0]	OPT_BITREVERSE =1'b0;
	generate if (OPT_BITREVERSE)
	begin : GEN_BITREVERSE
		// Arrange for (optionally) bit reversing the input
		//
		wire	[9:0]	brev_input;

		assign	brev_input[0] = i_word[9];
		assign	brev_input[1] = i_word[8];
		assign	brev_input[2] = i_word[7];
		assign	brev_input[3] = i_word[6];
		assign	brev_input[4] = i_word[5];
		assign	brev_input[5] = i_word[4];
		assign	brev_input[6] = i_word[3];
		assign	brev_input[7] = i_word[2];
		assign	brev_input[8] = i_word[1];
		assign	brev_input[9] = i_word[0];

		assign	w_in_word = brev_input;
	end else begin : NO_BITREVERSE
		assign	w_in_word = i_word;
	end endgenerate
	// }}}

	// (Optionally) delay the output bits
	// {{{
	localparam	DLY = 0;
	generate if (DLY != 0)
	begin
		reg	[(DLY-1):0]	r_word, d_word;

		always @(posedge i_clk)
			r_word <= w_in_word[(DLY-1):0];
		always @(posedge i_clk)
			d_word <= { r_word, w_in_word[9:DLY] };

		assign	w_word = d_word;
	end else begin : ZERO_DELAY
		assign	w_word = w_in_word;
	end endgenerate
	// }}}

	OSERDESE2	#(		 // Master SERDES, for the upper bits
		// {{{
		.DATA_RATE_OQ("DDR"),
		.DATA_RATE_TQ("SDR"),
		.DATA_WIDTH(10),
		.SERDES_MODE("MASTER"),
		.TRISTATE_WIDTH(1)	// Really ... this is unused
		// }}}
	) lowserdes(
		// {{{
		// Verilator lint_off PINCONNECTEMPTY
		.OCE(1'b1),	.OFB(),
		.TCE(1'b0),	.TFB(), .TQ(),
		.CLK(i_hsclk),	// HS clock
		.CLKDIV(i_clk),
		.OQ(w_hs_wire),
		.D1(w_word[9]),
		.D2(w_word[8]),
		.D3(w_word[7]),
		.D4(w_word[6]),
		.D5(w_word[5]),
		.D6(w_word[4]),
		.D7(w_word[3]),
		.D8(w_word[2]),
		.RST(!sync_reset_n),
		.TBYTEIN(1'b0), .TBYTEOUT(),
		.T1(1'b0), .T2(1'b0), .T3(1'b0), .T4(1'b0),
		.SHIFTIN1(slave_to_master[0]), .SHIFTIN2(slave_to_master[1]),
		.SHIFTOUT1(), .SHIFTOUT2()
		// Verilator lint_on  PINCONNECTEMPTY
		// }}}
	);

	OSERDESE2	#(	 // Slave SERDES, for the lower two bits
		// {{{
		.DATA_RATE_OQ("DDR"),
		.DATA_WIDTH(10),
		.DATA_RATE_TQ("SDR"),
		.SERDES_MODE("SLAVE"),
		.TRISTATE_WIDTH(1)	// Really ... this is unused
		// }}}
	) hiserdes(
		// {{{
		// Verilator lint_off PINCONNECTEMPTY
		.OCE(1'b1),	.OFB(), .OQ(),
		.TCE(1'b0),	.TFB(), .TQ(),
		.CLK(i_hsclk),	// HS clock
		.CLKDIV(i_clk),
		.D1(1'h0),
		.D2(1'h0),
		.D3(w_word[1]),
		.D4(w_word[0]),
		.D5(1'h0),
		.D6(1'h0),
		.D7(1'h0),
		.D8(1'h0),
		.RST(!sync_reset_n),
		.TBYTEIN(1'b0), .TBYTEOUT(),
		.T1(1'b0), .T2(1'b0), .T3(1'b0), .T4(1'b0),
		.SHIFTIN1(1'b0), .SHIFTIN2(1'b0),
		.SHIFTOUT1(slave_to_master[0]), .SHIFTOUT2(slave_to_master[1])
		// Verilator lint_on  PINCONNECTEMPTY
		// }}}
	);

	// Turn this high speed output into a pair of differential pins
	OBUFDS	hdmibuf(.I(w_hs_wire), .O(o_port[1]), .OB(o_port[0]));

endmodule
