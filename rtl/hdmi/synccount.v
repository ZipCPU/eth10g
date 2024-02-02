////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/synccount.v
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
//
`default_nettype	none
// }}}
module	synccount #(
		// {{{
		// (i_clk, i_reset, i_v, i_val, o_val);
		// NBITS -- num bits required to desecribe the sync location
		parameter		NBITS=16,
		// QUALITY_BITS --require 2^QUALITY_BITS successful observations
		parameter		QUALITY_BITS=3,
		// INITIAL_GOOD -- do we expect a particular sync?  Y/N
		parameter [0:0]		INITIAL_GOOD = 1'b0,
		// INITIAL_VALUE-- what initial sync location is expected
		parameter [(NBITS-1):0]	INITIAL_VALUE = 0,
		// INITIAL_COUNT-- how much credibility for initial location
		parameter [QUALITY_BITS-1:0]	INITIAL_COUNT = 0,
		// Shall we just bypass the quality test completely?
		parameter [0:0]		OPT_BYPASS_TEST = 1'b0
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		// i_v - valid sync indicator.  If (whatever) synchronization
		// is found at position i_val in the stream, then i_v will be
		// set.  We'll see how often it gets set to know if this is
		// (or isn't) a repeatable measurement.
		input	wire			i_v,
		input	wire	[NBITS-1:0]	i_val,
		output	reg	[NBITS-1:0]	o_val
		// }}}
	);

	generate if (OPT_BYPASS_TEST)
	begin : BYPASS_CHECK
		always @(posedge i_clk)
		if (i_v)
			o_val <= i_val;

		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, i_reset };
		// Verilator lint_on  UNUSED
	end else begin : REQUIRE_QUALITY
		reg			inc, dec;
		reg [QUALITY_BITS-1:0]	ngood;
		reg	[(NBITS-1):0]	r_val;

		reg	r_eq, no_val, r_v;

		initial	r_v = 1'b0;
		always @(posedge i_clk)
			r_v <= i_v;

		initial	r_eq = 1'b0;
		always @(posedge i_clk)
			r_eq <= (i_val == r_val);

		initial	no_val = (!INITIAL_GOOD);
		always @(posedge i_clk)
			no_val <= (ngood == 0);

		initial	r_val = INITIAL_VALUE;
		always @(posedge i_clk)
		if ((r_v)&&(no_val))
			r_val <= i_val;

		initial	inc = 1'b0;
		initial	dec = 1'b0;
		always @(posedge i_clk)
		begin
			inc  <= (!i_reset)&&(r_v)&&((r_eq)||(no_val));
			dec  <= (!i_reset)&&(r_v)&&(!r_eq);
		end

		initial	ngood = INITIAL_COUNT;
		always @(posedge i_clk)
		if (i_reset)
			ngood <= 0;
		else if ((inc)&&(!(&ngood)))
			ngood <= ngood + 1'b1;
		else if ((dec)&&(ngood != 0))
			ngood <= ngood - 1'b1;

		initial	o_val = INITIAL_VALUE;
		always @(posedge i_clk)
		if (&ngood)
			o_val <= r_val;
		else if (ngood == 0)
			o_val <= 0;
	end endgenerate
endmodule
