////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	fwb_register.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	While it may be fairly easy to verify that a core follows the
//		bus protocol, it's another thing to prove that the answers it
//	returns are the right ones.
//
//	This core is meant to be a complement to the fwb_slave logic, for slaves
//	that consist of a series of registers.  This core will test whether a
//	register can be written to using Wishbone, and/or read back properly
//	later.  It assumes a register having a single clock latency.
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
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
// }}}
//	http://www.apache.org/licenses/LICENSE-2.0
// {{{
// Unless required by applicable law or agreed to in writing, files
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
// }}}
module	fwb_register #(
		// {{{
		parameter		AW = 4,
		parameter		DW = 32,
		parameter [AW-1:0]	ADDR = 0,
		parameter [DW-1:0]	MASK = -1,
		parameter [DW-1:0]	FIXED_BIT_MASK = 0
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_wb_stb, i_wb_we,
		input	wire	[AW-1:0]	i_wb_addr,
		input	wire	[DW-1:0]	i_wb_data,
		input	wire	[DW/8-1:0]	i_wb_sel,
		input	wire			i_wb_ack,
		input	wire	[DW-1:0]	i_wb_return,
		input	wire	[DW-1:0]	i_register
		// }}}
	);

	// Local register, reset assumption
	// {{{
	integer			ik;
	reg			f_past_valid, past_reset;
	reg	[DW-1:0]	freg, non_ro_write, mask_write;
	wire	[DW-1:0]	error_mask;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(*)
		assert((MASK & FIXED_BIT_MASK) == 0);
	// }}}

	// freg
	// {{{
	always @(*)
	begin
		mask_write = (i_reset || past_reset) ? i_register : freg;
		for(ik=0; ik<DW/8; ik=ik+1)
		if (i_wb_sel[ik])
			mask_write[ik*8 +: 8] = i_wb_data[ik*8 +: 8];

		non_ro_write = (mask_write & ~FIXED_BIT_MASK)
				| (freg & FIXED_BIT_MASK);
	end

	initial	past_reset = 1'b1;
	always @(posedge i_clk)
		past_reset <= i_reset;

	always @(posedge i_clk or posedge i_reset)
	if (i_reset)
		freg <= i_register;
	else if (i_wb_stb && i_wb_we && i_wb_addr == ADDR)
		freg <= non_ro_write;
	else if (past_reset)
		freg <= i_register;
	// }}}

	// Comparing freg against i_register
	// {{{
	assign	error_mask = (freg ^ i_register) & MASK;

	always @(posedge i_clk)
	if (!i_reset && !past_reset)
		assert(error_mask == 0);
	// }}}

	// Verifying wb_ack
	// {{{
	always @(posedge i_clk)
	if (!i_reset && $past(!i_reset && i_wb_stb))
		assert(i_wb_ack);
	else if (!i_reset)
		assert(!i_wb_ack);
	// }}}

	// Verifying i_wb_return
	// {{{
	always @(posedge i_clk)
	if (!i_reset && $past(!i_reset && i_wb_stb && !i_wb_we
			&& i_wb_addr == ADDR))
		assert(i_wb_return == $past(i_register));
	// }}}

endmodule
