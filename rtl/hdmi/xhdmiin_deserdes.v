////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/xhdmiin_deserdes.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A Xilinx 1:10 ISERDES configuration, sufficient to support
//		reading a 10-bit HDMI word.  The ISERDES is done blindly,
//	according to an external clock which may (or may not) be aligned with
//	the data.  In the case where it is not aligned, a Xilinx 7-series IDELAY
//	is used to adjust the relationship between the data and the clock.
//	Bit order is such that o_word[9] is the *first* bit received, whereas
//	o_word[0] is the last.
//
//	This routine by itself is not sufficient.  An external routine may
//	be required to determine the proper IDELAY amount.  This should be
//	handled in hardware, but I've often resorted to doing this in software.
//	Likewise, an external synchronizer is required to determine which output
//	bits in the o_word stream constitute a 10-bit HDMI word.  This is
//	handled (currently) by the hdmipixelsync.v module.  A third
//	synchronizer, found in my hdmi2vga.v module is required to handle any
//	case where the words from the various color streams need to be further
//	aligned.
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
module	xhdmiin_deserdes #(
		parameter	DELAYSRC = "IDATAIN", IOBDELAY="IFD"
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_hsclk,
		input	wire		i_reset_n,
		input	wire	[4:0]	i_delay,
		output	wire	[4:0]	o_delay,
		input	wire		i_pin,
		output	wire		o_wire,
		output	reg	[9:0]	o_word
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[0:0]	OPT_BITREVERSE = 1'b0; // (Not required)

	wire	[5:0]	ignored_data;
	wire	[1:0]	master_to_slave;
	wire		ignored_output_hi;

	wire	w_hs_delayed_wire, w_hs_wire;
	wire	[9:0]	w_word;

	(* ASYNC_REG="TRUE" *)	wire		async_reset;
	(* ASYNC_REG="TRUE" *)	reg	[2:0]	reset_pipe;

	wire		lcl_ce;
	wire	[9:0]	w_use_this_word;
	// }}}

	// Synchronize the reset
	// {{{
	always @(posedge i_clk, negedge i_reset_n)
	if (!i_reset_n)
		reset_pipe[2:0] <= 3'h7;
	else
		reset_pipe[2:0] <= { reset_pipe[1:0], 1'b0 };
	assign	async_reset = reset_pipe[2];
	// }}}

	assign	lcl_ce = 1'b1;
	// }}}

	// Optionally delay the incoming signal
	// {{{
	generate if (IOBDELAY == "NONE")
	begin

		assign w_hs_wire         = i_pin;
		assign w_hs_delayed_wire = 1'b0;

	end else begin

		assign w_hs_wire = 1'b0;

		IDELAYE2	#(
			.CINVCTRL_SEL("FALSE"),
			.DELAY_SRC(DELAYSRC),
			.HIGH_PERFORMANCE_MODE("TRUE"),
			.REFCLK_FREQUENCY(300.0),
			.IDELAY_TYPE("VAR_LOAD")
		) delay(
			.C(i_clk), 
			.CE(1'b1),
			.CINVCTRL(1'b0),
			//
			.CNTVALUEIN(i_delay),
			.CNTVALUEOUT(o_delay),
			.LD(1'b1),
			.LDPIPEEN(1'b0),
			.REGRST(1'b0),
			.DATAIN(),
			.DATAOUT(w_hs_delayed_wire),
			.INC(1'b0),
			.IDATAIN(i_pin)
		);

	end endgenerate
	// }}}

	ISERDESE2	#(	// Master ISERDES for lower bits
		// {{{
		.SERDES_MODE("MASTER"),
		//
		.DATA_RATE("DDR"),
		.DATA_WIDTH(10),
		.INTERFACE_TYPE("NETWORKING"),
		.IOBDELAY(IOBDELAY),
		//
		.NUM_CE(1),
		.INIT_Q1(1'b0), .INIT_Q2(1'b0),
		.INIT_Q3(1'b0), .INIT_Q4(1'b0),
		.SRVAL_Q1(1'b0), .SRVAL_Q2(1'b0),
		.SRVAL_Q3(1'b0), .SRVAL_Q4(1'b0),
		.DYN_CLKDIV_INV_EN("FALSE"),
		.DYN_CLK_INV_EN("FALSE"),
		.OFB_USED("FALSE")
		// }}}
	) lowserdes(
		// {{{
		.BITSLIP(1'b0),
		.CE1(lcl_ce), .CE2(),
		.CLK(i_hsclk), .CLKB(!i_hsclk),	// HS clocks
		.CLKDIV(i_clk), .CLKDIVP(1'b0),
		.D(w_hs_wire), .DDLY(w_hs_delayed_wire), .DYNCLKDIVSEL(1'b0), .DYNCLKSEL(1'b0),
		.O(o_wire), .OCLK(1'b0), .OCLKB(1'b0), .OFB(1'b0),
		.Q1(w_word[0]),
		.Q2(w_word[1]),
		.Q3(w_word[2]),
		.Q4(w_word[3]),
		.Q5(w_word[4]),
		.Q6(w_word[5]),
		.Q7(w_word[6]),
		.Q8(w_word[7]),
		.RST(async_reset),
		.SHIFTIN1(1'h0), .SHIFTIN2(1'h0),
		.SHIFTOUT1(master_to_slave[0]), .SHIFTOUT2(master_to_slave[1])
		// }}}
	);

	ISERDESE2	#(	// Slave ISERDES for the upper bits
		// {{{
		.SERDES_MODE("SLAVE"),
		//
		.DATA_RATE("DDR"),
		.DATA_WIDTH(10),
		.INTERFACE_TYPE("NETWORKING"),
		.IOBDELAY("NONE"),
		//
		.NUM_CE(1),
		.INIT_Q1(1'b0), .INIT_Q2(1'b0),
		.INIT_Q3(1'b0), .INIT_Q4(1'b0),
		.SRVAL_Q1(1'b0), .SRVAL_Q2(1'b0),
		.SRVAL_Q3(1'b0), .SRVAL_Q4(1'b0),
		.DYN_CLKDIV_INV_EN("FALSE"),
		.DYN_CLK_INV_EN("FALSE"),
		.OFB_USED("FALSE")
		// }}}
	) hiserdes(
		// {{{
		.BITSLIP(1'b0),
		.CE1(lcl_ce), .CE2(),
		.CLK(i_hsclk), .CLKB(!i_hsclk),	// HS clocks
		.CLKDIV(i_clk), .CLKDIVP(1'b0),
		.D(), .DDLY(), .DYNCLKDIVSEL(1'b0), .DYNCLKSEL(1'b0),
		.O(ignored_output_hi), .OCLK(1'b0), .OCLKB(1'b0), .OFB(1'b0),
		.Q1(),
		.Q2(),
		.Q3(w_word[8]),
		.Q4(w_word[9]),
		.Q5(),
		.Q6(),
		.Q7(),
		.Q8(),
		// .Q7(w_word[8]),
		// .Q8(w_word[9]),
		.RST(async_reset),
		.SHIFTIN1(master_to_slave[0]), .SHIFTIN2(master_to_slave[1]),
		.SHIFTOUT1(), .SHIFTOUT2()
		// }}}
	);

	// (Optionally) bit reverse our incoming data (we don't need to do this)
	// {{{
	generate if (OPT_BITREVERSE)
	begin
		wire	[9:0]	w_brev;

		assign	w_brev[9] = w_word[0];
		assign	w_brev[8] = w_word[1];
		assign	w_brev[7] = w_word[2];
		assign	w_brev[6] = w_word[3];
		assign	w_brev[5] = w_word[4];
		assign	w_brev[4] = w_word[5];
		assign	w_brev[3] = w_word[6];
		assign	w_brev[2] = w_word[7];
		assign	w_brev[1] = w_word[8];
		assign	w_brev[0] = w_word[9];

		assign	w_use_this_word = w_brev;
	end else begin
		assign	w_use_this_word = w_word; // w_brev;
	end endgenerate
	// }}}

	// Optionally delay align these bits.
	// {{{
	// Turns out ... we don't need to do this here.
	localparam	[3:0]	DLY = 0;
	generate if (DLY != 0)
	begin
		reg	[(DLY-1):0]	r_word;
		always @(posedge i_clk)
			r_word <= w_use_this_word[(DLY-1):0];
		always @(posedge i_clk)
			o_word <= { r_word[(DLY-1):0],w_use_this_word[9:(DLY)]};
	end else
		always @(posedge i_clk)
			o_word <= w_use_this_word;
	endgenerate
	// }}}
endmodule
