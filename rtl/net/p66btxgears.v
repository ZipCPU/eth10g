////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/p66btxgears.v
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
module	p66btxgears // #()
	(
		// {{{
		input	wire	i_clk,
		input	wire	i_reset,
		//
		// input wire		S_VALID,
		output	reg		S_READY,
		input	wire	[65:0]	S_DATA,
		//
		output	wire	[31:0]	o_data
		// }}}
	);

	reg	[6:0]	r_count;
	reg	[95:0]	gearbox;
	reg	[127:0]	full_gears;

	always @(posedge i_clk)
	if (i_reset)
	begin
		r_count <= 0;
		S_READY <= 1;
	end else if (S_READY)
	begin
		r_count <= r_count + 66 - 32;
		S_READY <= (r_count + 34) < 64;
	end else begin
		if (r_count > 32)
			r_count <= r_count - 32;
		else
			r_count <= 0;
		S_READY <= (r_count < 96);
	end

	always @(*)
	begin
		full_gears = 0;
		full_gears[95:0] = gearbox;
		if (S_READY)
			full_gears = full_gears
					| ({ 62'h0, S_DATA} << r_count);
		full_gears = full_gears >> 32;
	end

	always @(posedge i_clk)
	if (i_reset)
		gearbox <= 96'h0;
	else
		gearbox <= full_gears[95:0];

	assign	o_data = gearbox[31:0];
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
// Note: this is (currently) only a partial proof
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(*)
	if (!i_reset)
	begin
		assert(r_count[0] == 1'b0);
		assert(r_count <= 64+32);
		assert(S_READY == (r_count < 64));
	end

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && $past(r_count >= 32))
	begin
		assert(r_count >= 32);
	end
`endif
// }}}
endmodule
