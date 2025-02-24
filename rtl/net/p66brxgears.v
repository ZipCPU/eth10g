////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/p66brxgears.v
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
module p66brxgears (
		// {{{
		input	wire	i_clk, i_reset,

		input	wire	[31:0]	i_data,
		output	wire		M_VALID,
		output	wire	[65:0]	M_DATA
		// }}}
	);

	// Local declarations
	// {{{
	localparam	LOCKMSB = 5;
	reg		rx_valid;
	reg	[6:0]	rx_count;
	reg	[95:0]	rx_gears;

	reg	[65:0]	al_last, al_data;
	reg	[65:0]	ign_al_msb;
	reg	[6:0]	al_shift;
	reg		al_slip;
	reg	[LOCKMSB:0]	lock_count;

	reg	[128-1:0]	full_set;
	reg	[31:0]	r_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step one: the gearbox
	// {{{

	// pre-state: register the data -- for timing's sake
	always @(posedge i_clk)
		r_data <= i_data;
	
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
				| ({ 96'h0, r_data } << rx_count);
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
		else if (al_data[0] != al_data[1])
		begin
			if (!lock_count[LOCKMSB])
				lock_count <= lock_count + 1;
		end else if (lock_count > 3)
			lock_count <= lock_count - 3;
		else begin
			lock_count <= 0;
			al_slip <= 1;
			if (al_shift >= 65)
				al_shift <= 0;
			else
				al_shift <= al_shift + 1;
		end
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset)
		assert(al_shift < 66);
	always @(*)
	if (!i_reset && lock_count[LOCKMSB])
		assert(lock_count[LOCKMSB-1:0] == 0);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step three: output
	// {{{
	assign	M_VALID = rx_valid && lock_count[LOCKMSB];
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

	always @(*) if (!f_past_valid) assume(i_reset);
	// always @(*)	assume(i_reset != f_past_valid);
	////////////////////////////////////////////////////////////////////////
	//
	// Ad-hoc properties
	// {{{
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
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[4:0]	f_pipe;
	reg	[6:0]	f_align_posn;
	reg	[31:0]	f_shift_idata, f_data;
	reg	[63:0]	f_align_idata;

	reg	[6:0]	fr_align_posn;
	reg	[31:0]	fr_data;
	reg	[63:0]	fr_shift_data;

	reg	[6:0]	frx_align_posn, frx_alignment;
	reg	[95:0]	frx_shift_data, frx_dblshift_data;

	reg	[6:0]	fal_align_posn;
	reg	[31:0]	fal_shift;

	////////////////////////////////////////
	//
	// Alignment contract
	// {{{
	//
	// Given alignment data arrives every 66 bits, prove that once we
	// align we keep alignment

	// f_pipe -- to know when each stage is valid
	// {{{

	always @(posedge i_clk)
	if (i_reset)
		f_pipe <= 0;
	else begin
		f_pipe[2:0] <= { f_pipe[1:0], 1'b1 };

		if (rx_valid)
			f_pipe[4:3] <= f_pipe[3:2];
	end

	always @(*)
	if (!i_reset)
	case(f_pipe)
	5'h00: begin end
	5'h01: begin end
	5'h03: begin end
	5'h07: begin end
	5'h0f: begin end
	5'h1f: begin end
	default: assert(0);
	endcase
	// }}}

	// Step 1. Assume two alignment bits every 66 on input
	// {{{
	initial	f_align_posn = 0;
	always @(posedge i_clk)
	if (f_align_posn < 32)
		f_align_posn <= f_align_posn + 66-32;
	else
		f_align_posn <= f_align_posn - 32;

	always @(*)
		assert(f_align_posn < 66+66-32);

	always @(posedge i_clk)
		f_data <= i_data;

	always @(*)
		f_align_idata = { i_data, f_data } >> f_align_posn;

	always @(*)
	if (f_align_posn < 63)
		assume(^f_align_idata[1:0]);
	// }}}

	// Step 2. Track from i_data to r_data
	// {{{
	initial	fr_align_posn = 0;
	always @(posedge i_clk)
	if (f_align_posn < 66)
		fr_align_posn <= f_align_posn;
	else
		fr_align_posn <= f_align_posn - 66;

	always @(posedge i_clk)
		fr_data <= r_data;

	always @(posedge i_clk)
	if (!i_reset)
		assert(f_data == r_data);

	always @(*)
		fr_shift_data = { r_data, fr_data } >> fr_align_posn;

	always @(*)
	if (!i_reset && f_pipe[1] && fr_align_posn < 63)
		assert(^fr_shift_data[1:0]);
	// }}}

	// Step 3. Track from r_data to rx_gears
	// {{{
	initial	frx_align_posn = 0;
	always @(posedge i_clk)
	if (rx_valid && (fr_align_posn + rx_count > 66 + 32))
		frx_align_posn <= fr_align_posn + rx_count - 66 - 32;
	else
		frx_align_posn <= fr_align_posn + rx_count - 32;

	always @(*)
		frx_shift_data = rx_gears >> frx_align_posn;

	always @(*)
	if (frx_align_posn > 66)
		frx_dblshift_data = rx_gears >> (frx_align_posn - 66);
	else
		frx_dblshift_data = rx_gears >> (66 + frx_align_posn);

	always @(posedge i_clk)
	if (!i_reset && f_pipe[2] && (frx_align_posn + 1 < rx_count))
		assert(^frx_shift_data[1:0]);

	always @(*)
	if (frx_align_posn >= 66)
		frx_alignment = frx_align_posn - 66;
	else
		frx_alignment = frx_align_posn;

//	always @(*)
//	if (f_pipe[3] && frx_align_posn > 66 && frx_align_posn - 66 < rx_count)
//		assert(^frx_dblshift_data[1:0]);

	always @(posedge i_clk)
	if (!i_reset && f_pipe[3])
		assert($stable(frx_alignment));
	// }}}

	// Step 3. Track from rx_gears to al_data
	// Step 4. Now *PROVE*: Once locked, always locked
	// {{{
	always @(posedge i_clk)
	if (rx_valid)
		fal_align_posn <= frx_alignment;

	always @(*)
		fal_shift = { rx_gears[65:0], al_last } >> fal_align_posn;

	always @(posedge i_clk)
	if (!i_reset && f_pipe[4] && (rx_valid || fal_align_posn < 65))
		assert(^fal_shift[1:0]);

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && $past(f_pipe[4]) && $past(al_shift) == fal_align_posn)
	begin
		// assert(f_locked);
		assert(!$rose(al_slip));
		assert($stable(al_shift));
	end
	// }}}
	// }}}

	////////////////////////////////////////
	//
	// Data contract
	// {{{
	//
	// Given arbitrary input data at an arbitrary point in time, prove
	// that this data ends up in the output at the same point in time
	(* anyconst *)	reg	[15:0]	fc_posn;
	(* anyconst *)	reg	[1:0]	fc_dblet;
	reg	[15:0]	fc0_posn;
	reg	[63:0]	fc0_shift;

	reg	[15:0]	fc1_posn;
	reg	[63:0]	fc1_shift;

	reg	[15:0]	fc2_posn;
	reg	[95:0]	fc2_shift;

	reg	[15:0]	fc3_posn;
	reg	[65:0]	fc3_shift;

	reg	[15:0]	falc_posn;
	reg	[65:0]	falc_shift;

	initial	fc0_posn = 0;
	always @(posedge i_clk)
		fc0_posn <= fc0_posn + 32;

	always @(*)
		fc0_shift = { i_data, f_data } >> (fc_posn-fc0_posn);

	always @(*)
	if (fc0_posn <= fc_posn && fc_posn <= fc0_posn + 32)
		assume(fc0_shift[1:0] == fc_dblet);

	initial	fc1_posn = -32;
	always @(posedge i_clk)
		fc1_posn <= fc0_posn;

	always @(*)
		fc1_shift = { r_data, fr_data } >> (fc_posn-fc1_posn);

	always @(*)
	if (!i_reset && f_pipe[0] && fc1_posn <= fc_posn && fc_posn + 1 < fc1_posn + 32)
		assert(fc1_shift[1:0] == fc_dblet);

	// fc2_posn is the position of the first bit of the rx_gears register
	initial	fc2_posn = 0;
	always @(posedge i_clk)
	if (rx_valid)
		fc2_posn <= fc0_posn - rx_count + 66;
	else
		fc2_posn <= fc0_posn - rx_count;


	always @(*)
		fc2_shift = rx_gears >> (fc_posn-fc2_posn);

	always @(*)
	if (!i_reset && f_pipe[2] && fc2_posn <= fc_posn && fc_posn + 1 < fc2_posn + rx_count)
		assert(fc2_shift[1:0] == fc_dblet);

	initial	fc3_posn = 0;
	always @(posedge i_clk)
	if (rx_valid)
		fc3_posn <= fc2_posn;

	always @(*)
		fc3_shift = al_last >> (fc_posn-fc3_posn);

	always @(*)
	if (!i_reset && f_pipe[3] && fc3_posn <= fc_posn && fc_posn + 1 < fc3_posn + 66)
		assert(fc3_shift[1:0] == fc_dblet);

	always @(posedge i_clk)
	if (rx_valid)
		falc_posn <= fc3_posn + al_shift;
	always @(*)
		falc_shift = { ign_al_msb, al_data } >> (fc_posn-falc_posn);
	always @(*)
	if (!i_reset && rx_valid && f_pipe[4] && falc_posn <= fc_posn && fc_posn + 1 < falc_posn + 66)
		assert(falc_shift[1:0] == fc_dblet);
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	always @(*)
	begin
		assume(fc_posn[15] == 1'b0);
		assume(fc_posn > 16'h80);
	end
	// }}}
`endif
// }}}
endmodule
