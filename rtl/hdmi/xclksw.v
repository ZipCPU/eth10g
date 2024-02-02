////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/xclksw.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A fault tolerant clock switch.
//
//	Xilinx provides BUFGCTRL elements which we use here.  We want a
//	capability similar to a BUFGMUX, save that we want to be able to switch
//	clocks even when one (or both) clocks are not present.  Hence a system
//	clock is required to drive a state machine and help guarantee a switch.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
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
// }}}
module	xclksw #(
		parameter [0:0] DEF_CLK = 1'b0
	) (
		// {{{
		input	wire	i_sys_clk,
		input	wire	i_clk_sel,
		input	wire	i_ck0, i_ck1,
		output	wire	o_clk
		// }}}
	);

	// Local declarations
	// {{{
	localparam [2:0]	CK_SET0   = 3'h0,
				CK_REQ1   = 3'h1,
				CK_FORCE1 = 3'h2,
				CK_SET1   = 3'h3,
				CK_REQ0   = 3'h4,
				CK_FORCE0 = 3'h5;
	reg	[2:0]	state;
	reg	[3:0]	ctr;
	reg		hard_0, hard_1, r_sel;
	// }}}

	BUFGCTRL #(
		// {{{
		.INIT_OUT(1'b0),
		.PRESELECT_I0(DEF_CLK ? "FALSE" : "TRUE"),
		.PRESELECT_I1(DEF_CLK ? "TRUE"  : "FALSE")
`ifndef	YOSYS
		, .SIM_DEVICE("7SERIES")
`endif
		// }}}
	) u_bufg (
		// {{{
		// Clock zero
		.CE0(1'b1), // could also force w/ (!r_sel || !hard_0),
		.IGNORE0(hard_0),
		.S0(!r_sel),
		.I0(i_ck0),
		//
		// Clock one
		.CE1(1'b1), // could also force w/ ( r_sel || !hard_1),
		.IGNORE1(hard_1),
		.S1(r_sel),
		.I1(i_ck1),
		//
		// Result
		.O(o_clk)
		// }}}
	);

	// State machine
	// {{{
	initial	begin
		state  = (DEF_CLK) ? CK_SET1 : CK_SET0;
		r_sel  = DEF_CLK;
		hard_0 = 1'b0;
		hard_1 = 1'b0;
		ctr    = 4'h0;
	end

	always @(posedge i_sys_clk)
	case(state)
	CK_SET0: begin
		// {{{
		hard_0 <= 1'b0;
		hard_1 <= 1'b0;
		if (ctr != 0)
			ctr <= ctr - 1;
		else if (i_clk_sel)
		begin
			state  <= CK_REQ1;
			r_sel  <= 1'b1;
			ctr    <= 4'hf;
		end else begin
			state  <= CK_SET0;
			r_sel  <= 1'b0;
			ctr    <= 4'h0;
		end end
		// }}}
	CK_REQ1: begin
		// {{{
		r_sel <= 1'b1;
		hard_0 <= 1'b0;
		hard_1 <= 1'b0;
		ctr <= ctr - 1;
		if (ctr == 0)
		begin
			state  <= CK_FORCE1;
		end end
		// }}}
	CK_FORCE1: begin
		// {{{
		r_sel  <= 1'b1;
		hard_0 <= 1'b1;
		hard_1 <= 1'b0;
		ctr <= ctr - 1;

		if (ctr == 0)
			state  <= CK_SET1;
		end
		// }}}
	CK_SET1: begin
		// {{{
		hard_0 <= 1'b0;
		hard_1 <= 1'b0;
		if (ctr != 0)
			ctr <= ctr - 1;
		else if (!i_clk_sel)
		begin
			// Transition to clock 0
			state  <= CK_REQ0;
			r_sel  <= 1'b0;
			ctr    <= 4'hf;
		end else begin
			// Stay at clock 1
			state  <= CK_SET1;
			r_sel  <= 1'b1;
			ctr    <= 4'h0;
		end end
		// }}}
	CK_REQ0: begin
		// {{{
		r_sel <= 1'b0;
		hard_0 <= 1'b0;
		hard_1 <= 1'b0;
		ctr <= ctr - 1;
		if (ctr == 0)
		begin
			state  <= CK_FORCE0;
		end end
		// }}}
	CK_FORCE0: begin
		// {{{
		r_sel  <= 1'b0;
		hard_0 <= 1'b0;
		hard_1 <= 1'b1;

		ctr <= ctr - 1;
		if (ctr == 0)
			state  <= CK_SET0;
		end
		// }}}
	default: begin
		// {{{
		state  <= (i_clk_sel) ? CK_SET1 : CK_SET0;
		hard_0 <= 1'b1;
		hard_1 <= 1'b1;
		ctr    <= 4'hf;
		end
		// }}}
	endcase
	// }}}
endmodule
