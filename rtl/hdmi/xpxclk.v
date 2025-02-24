////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/xpxclk.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Contains the Xilinx specific portions of HDMI ingestion.
//
//	Specifically, this includes:
//	1. Turning our incoming clocks from double ended to single ended via
//		a Xilinx IBUFDS.
//	2. Selecting from among three clocks for our pixel clock.  The pixel
//		clock will therefore be one of: 1) an internal 40MHz reference,
//		2) an external reference from an Si5324 frequency generator,
//		or 3) an external reference from an external/incoming HDMI RX
//		port.
//	3. Once selected, pixel clock is then pushed into a PLL to generate the
//		5x pixel clock signal required for HDMI.  (It's not 10x, since
//		the HDMI input/output SERDES use DDR mode, so it only needs
//		to be half that.)
//	4. The pixel clock and 5x clock are then pushed through BUFGs and
//		output.
//
//	NOTE this design uses 5 BUFGs.
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
module	xpxclk (
		// {{{
		input	wire		i_sysclk,
		input	wire		i_hdmirx_clk_p, i_hdmirx_clk_n,
		input	wire		i_lcl_pixclk,
		input	wire		i_siclk,
		input	wire	[1:0]	i_cksel,
		output	wire		o_hdmick_locked,
		output	wire		o_hdmirx_clk,
		output	wire		o_pixclk, o_hdmick
		// }}}
	);

	// Local declarations
	// {{{
	wire	lclck, hdmirx_ck, preck;
	wire	clk_fbout, clk_fb, pixclk_nobuf, hdmi_ck;
	// }}}

	// Select lclck from either i_lcl_pixclk or i_siclk
	// {{{
`define	SICLK
`ifdef	SICLK
	xclksw
	lclpx (
		.i_sys_clk(i_sysclk), .i_clk_sel(i_cksel[0]),
		.i_ck0(i_lcl_pixclk), .i_ck1(i_siclk), .o_clk(lclck)
	);
`else
	assign	siclk   = i_lcl_pixclk;
	assign	lclck   = i_lcl_pixclk;
`endif
	// }}}

	// Select preck from either lclck or hdmirx_clk
	// {{{
	IBUFDS
	ibuf_hdmi_ck (
		.I(i_hdmirx_clk_p), .IB(i_hdmirx_clk_n), .O(hdmirx_ck)
	);

	assign	o_hdmirx_clk = hdmirx_ck;

	xclksw
	prepx (
		.i_sys_clk(i_sysclk), .i_clk_sel(i_cksel[1]),
		.i_ck0(lclck), .i_ck1(hdmirx_ck), .o_clk(preck)
	);
	// }}}

	PLLE2_BASE #(
		// {{{
		.CLKFBOUT_MULT(10),
		.CLKFBOUT_PHASE(0.0),
		.CLKIN1_PERIOD(6.6),	// Up to 200MHz input
		.CLKOUT0_DIVIDE(10),
		.CLKOUT1_DIVIDE(2)
		// }}}
	) u_hdmi_pll (
		// {{{
		.CLKIN1(preck),		// Incoming clock
		.PWRDWN(1'b0),
		.CLKFBIN(clk_fb),
		.CLKFBOUT(clk_fbout),
		.LOCKED(o_hdmick_locked),
		//
		.CLKOUT0(pixclk_nobuf),
		.CLKOUT1(hdmi_ck)
		// }}}
	);

	BUFG fdback_buf( .I(clk_fbout),    .O(clk_fb));
	BUFG pixclk_buf( .I(pixclk_nobuf), .O(o_pixclk));
	BUFG hdmi_buf(   .I(hdmi_ck),      .O(o_hdmick));

endmodule
