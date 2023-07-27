////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	p66rxgears.v
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
`default_nettype none
// }}}
module p66brxgears (
		input	wire	i_clk, i_reset,

		input	wire	[31:0]	i_data,
		output	wire		M_VALID,
		output	wire	[65:0]	M_DATA
	);

	// Local declarations
	// {{{
	reg		rx_valid;
	reg	[6:0]	rx_count;
	reg	[95:0]	rx_gears;

	reg	[65:0]	al_last, al_data, ign_al_msb;
	reg	[6:0]	al_shift;
	reg		al_slip;
	reg	[3:0]	lock_count;

	reg	[128-1:0]	full_set;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step one: the gearbox
	// {{{

	// { rx_count } = # of bits in our shift register
	// rx_valid = (66 or more bits in the shift register)
	always @(posedge i_clk)
	if (i_reset)
	begin
		rx_count <= 0;
		rx_valid <= 0;
	end else if (rx_valid)
	begin
		rx_count <= rx_count + 32 - 66;
		rx_valid <= 1'b0;	// i.e. if (rx_count  + 32 - 66 >= 66)
	end else begin
		rx_count <= rx_count + 32;	// Always add 32
		rx_valid <= (rx_count >= 34);
	end

	always @(*)
	begin
		full_set = { 32'h0, rx_gears }
				| ({ 96'h0, i_data } << rx_count);
		if (rx_valid)
			full_set = full_set >> 66;
	end

	always @(posedge i_clk)
	if (i_reset)
		rx_gears <= 0;
	else
		rx_gears <= full_set[95:0];
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step two: alignment
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		al_last <= 0;
	else if (rx_valid)
		al_last <= rx_gears[65:0];

	always @(posedge i_clk)
	// if (i_reset)
	//	{ ign_al_msb, al_data } <= 0;
	// else
	if (rx_valid)
		{ign_al_msb, al_data } <= { rx_gears[65:0],al_last } >>al_shift;

	
	always @(posedge i_clk)
	if (i_reset)
	begin
		lock_count <= 0;
		al_slip <= 0;
		al_shift <= 0;
	end else if (rx_valid)
	begin
		if (al_slip)
			al_slip <= 0;
		else if (al_data[0] !== al_data[1])
		begin
			if (lock_count + 1 < 16)
				lock_count <= lock_count + 1;
		end else if (lock_count > 3)
			lock_count <= lock_count - 3;
		else begin
			lock_count <= 0;
			al_slip <= 1;
			if (al_shift > 65)
				al_shift <= 0;
			else
				al_shift <= al_shift + 1;
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step three: output
	// {{{
	assign	M_VALID = rx_valid && lock_count[3];
	assign	M_DATA  = al_data;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ign_al_msb };
	// Verilator lint_on  UNUSED
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
	// The following isn't a *full* formal proof, but it was enough
	// to get me past some bugs I just couldn't figure my way through.
	reg	f_past_valid;
	integer	ik;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(*)
	if (!i_reset)
	begin
		assert(rx_count <= 96);
		assert(rx_count[0] == 1'b0);
		assert(rx_valid == (rx_count >= 66));
	end

	always @(*)
	if (!i_reset)
		assert(full_set[127:96] == 0);

	always @(*)
	if (!i_reset)
	begin
		for(ik=0; ik<96; ik=ik+1)
		if (rx_count <= ik)
			assert(rx_gears[ik] == 1'b0);
	end
`endif
// }}}
endmodule
