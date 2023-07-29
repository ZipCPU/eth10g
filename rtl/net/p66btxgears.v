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
		output	wire		S_READY,
		input	wire	[65:0]	S_DATA,
		//
		input	wire		i_ready,
		output	wire	[63:0]	o_data
		// }}}
	);

	// Local declarations
	// {{{
	reg	[7:0]		r_count;
	reg	[127:0]		gearbox;
	reg	[128+64-1:0]	full_gears;
	wire	[5:0]		shift;
	// }}}

	always @(posedge i_clk)
	if (i_reset)
	begin
		r_count <= 0;	// = 64
	end else if (i_ready)
	begin
		if (!r_count[5])
			r_count <= r_count + 1;
		else
			r_count <= r_count - 32;
	end
	assign	shift = { r_count[4:0], 1'b0 };
	assign	S_READY = (!r_count[5] && i_ready);

	always @(*)
	begin
		full_gears = 0;
		full_gears[127:0] = gearbox;
		if (!r_count[5])
			full_gears = full_gears
				| ({ 62'h0, S_DATA, 64'h0 } << shift);
		full_gears = full_gears >> 64;
	end

	always @(posedge i_clk)
	if (i_reset)
		gearbox <= 128'h0;
	else if (i_ready)
		gearbox <= full_gears[127:0];

	assign	o_data = gearbox[63:0];
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
	// assign	f_count = { r_count, 1'b0 } + 64;

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
		assert(r_count <= 64+64);
		assert(pre_ready == (r_count < 128));
	end

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && !$past(S_READY))
		assume($stable(S_DATA));

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && !$past(i_ready))
	begin
		assert($stable(r_count));
		assert($stable(pre_ready));
		assert($stable(o_data));
	end

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && $past(r_count >= 64))
	begin
		assert(r_count >= 64);
	end
`endif
// }}}
endmodule
