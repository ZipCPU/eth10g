////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/p66btxgears.v
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
	(* anyconst *)	reg	[18:0]	fc_posn;
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
	else if (i_ready)
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
		assume(fc_posn == fs_posn);

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
			&& shift >= 66
			&& fc_posn < fg_posn + f_count && f_pipe[2])
		assert(0 == ((fc_shift ^ f_shifted[65:0]) & f_mask));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{

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
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{

	always @(posedge i_clk)
	if (!$past(i_ready))
		assume(i_ready);

	// }}}
`endif
// }}}
endmodule
