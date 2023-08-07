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
	reg	[7:0]	f_count;
	reg		f_past_valid;
	(* anyconst *)	reg	[18:0]	fc_posn
	(* anyconst *)	reg	[65:0]	fc_data;
	(* anyconst *)	reg		fc_check;
	reg	[18:0]	fs_posn, fg_posn, f_offset;
	reg	[127:0]	f_shifted;
	reg	[65:0]	fc_shift, f_mask;
	reg	[3:0]	f_pipe;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	////////////////////////////////////////////////////////////////////////
	//
	// Gearbox
	// {{{
	always @(*)
		f_count = shift;

	always @(*)
	if (!i_reset)
	begin
		assert(shift[0] == 1'b0);
		assert(shift <= 64+64);
		// assert(pre_ready == (r_count < 128));
	end

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && !$past(S_READY))
		assume($stable(S_DATA));

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && !$past(i_ready))
	begin
		assert($stable(f_count));
		// assert($stable(pre_ready));
		assert($stable(o_data));
	end

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && $past(f_count >= 64))
	begin
		assert(f_count >= 64);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract
	// {{{
	// Start ... by counting.

	always @(posedge i_clk)
	if (i_reset)
		f_pipe <= 0;
	else
		f_pipe <= { f_pipe[2:0], 1'b1 };

	always @(posedge i_clk)
	if (i_reset)
		fs_posn <= 0;
	else if (S_READY)
		fs_posn <= fs_posn + 66;

	always @(posedge i_clk)
	if (i_reset)
		fg_posn <= 0;
	else if (S_READY)
		fg_posn <= fs_posn - shift;
	else if (i_ready)
		fg_posn <= fg_posn+64;

	// 
	// Without a little help, it's not clear we'd ever land on one of
	// our items.  Therefore, let's assume fc_posn becomes valid at some
	// point, and doesn't get skipped.
	always @(*)
	if (fs_posn <= fc_posn && fc_posn < fs_posn+66)
		assume(fc_data == fs_posn);

	// Finally, ASSUME the given data when we hit the given count.
	always @(*)
	if (fc_check && fs_posn == fc_posn)
		assume(fc_data == S_DATA);

	always @(*)
	if (fc_posn > fg_posn)
		f_offset = fc_posn - fg_posn;
	else
		f_offset = 0;

	always @(*)
		f_shifted = (gearbox >> f_offset);
	always @(*)
	if (fc_posn >= fg_posn)
		fc_shift = fc_data;
	else
		fc_shift = fc_data >> (fg_posn - fc_posn);

	always @(*)
	if (fc_posn+66 < fg_posn && fg_posn > fc_posn)
		f_mask = {(66){1'b1}} >> (fg_posn-fc_posn);
	else // if (fc_posn >= fg_posn)
		f_mask = {(66){1'b1}};

	always @(posedge i_clk)
	if (!i_reset && fc_check && fg_posn <= fc_posn+66
			&& fc_posn < fg_posn + f_count && f_pipe[2])
		assert(0 == ((fc_shift ^ f_shifted[65:0]) & f_mask));

	// Let's just make sure we can do this properly ...
	always @(*)
	if (!i_reset)
	begin
		cover(fc_posn == 132 && fg_posn > 132 + 130);
		cover(fc_posn == 198 && fg_posn > 198 + 130);
		cover(fc_posn == 264 && fg_posn > 264 + 130);
		cover(fc_posn == 330 && fg_posn > 330 + 130);
		cover(fc_posn == 396 && fg_posn > 396 + 130);
		cover(fc_posn == 462 && fg_posn > 462 + 130);
	end

	// }}}
`endif
// }}}
endmodule
