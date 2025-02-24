////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/vid_empty.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generates an outgoing video stream, having all the proper
//		video stream signals, but with a constant pixel value.
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
module	vid_empty #(
		// {{{
		parameter		PW = 24,
		parameter		LGFRAME = 12,
		parameter [PW-1:0]	PIXEL = 0,
		parameter [0:0]		OPT_TUSER_IS_SOF = 1
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		//
		input	wire	[LGFRAME-1:0]	i_width, i_height,
		//
		output	reg			M_VID_VALID,
		input	wire			M_VID_READY,
		output	wire	[PW-1:0]	M_VID_DATA,
		output	wire			M_VID_LAST,
		output	wire			M_VID_USER
		// }}}
	);

	// Local declarations
	// {{{
	reg			hlast, vlast;
	reg	[LGFRAME-1:0]	xpos, ypos;
	// }}}

	// M_VID_VALID
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		M_VID_VALID <= 0;
	else
		M_VID_VALID <= 1;
	// }}}

	assign	M_VID_DATA = PIXEL;

	// xpos, ypos, hlast, vlast
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		xpos  <= 0;
		ypos  <= 0;
		hlast <= 0;
		vlast <= 0;
	end else if (M_VID_VALID && M_VID_READY)
	begin
		xpos <= xpos + 1;
		hlast <= (xpos >= i_width-2);

		if (hlast)
		begin
			hlast <= 0;
			xpos  <= 0;
			vlast <= (ypos >= i_height-2);
			ypos  <= ypos + 1;

			if (vlast)
			begin
				vlast <= 0;
				ypos  <= 0;
			end
		end
	end
	// }}}

	generate if (OPT_TUSER_IS_SOF)
	begin : GEN_SOF
		reg	sof;

		always @(posedge i_clk)
		if (i_reset)
			sof <= 1;
		else if (M_VID_VALID && M_VID_READY)
			sof <= hlast && vlast;

		assign	M_VID_LAST = hlast;
		assign	M_VID_USER = sof;
`ifdef	FORMAL
		always @(*)
		if (!i_reset)
			assert(sof == (xpos == 0 && ypos == 0));
`endif
	end else begin : GEN_VLAST
		assign	M_VID_LAST = vlast & hlast;
		assign	M_VID_USER = hlast;
	end endgenerate
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
	reg	f_past_valid;
	wire	[LGFRAME-1:0]	f_xpos, f_ypos;
	wire			f_hlast, f_vlast, f_sof, f_known_height;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if (!i_reset)
	begin
		assume($stable(i_width));
		assume($stable(i_height));

		assume(i_width  > 2);
		assume(i_height > 2);
	end

	faxivideo #(
		// {{{
		.PW(PW), .LGDIM(LGFRAME), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) fvid (
		// {{{
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.S_VID_TVALID(M_VID_VALID),
		.S_VID_TREADY(M_VID_READY),
		.S_VID_TDATA(M_VID_DATA),
		.S_VID_TLAST(M_VID_LAST),
		.S_VID_TUSER(M_VID_USER),
		//
		.i_width(i_width), .i_height(i_height),
		.o_xpos(f_xpos), .o_ypos(f_ypos),
		.f_known_height(f_known_height),
		.o_hlast(f_hlast), .o_vlast(f_vlast), .o_sof(f_sof)
		// }}}
	);

	always @(*)
	if (!i_reset)
	begin
		assert(xpos == f_xpos);
		assert(ypos == f_ypos);
		assert(hlast == f_hlast);
		assert(vlast == f_vlast);
	end

	always @(*)
		cover(!i_reset && M_VID_VALID && hlast && vlast);

	generate if (OPT_TUSER_IS_SOF)
	begin
		always @(posedge i_clk)
			cover(!i_reset && M_VID_VALID && $rose(M_VID_USER));
	end endgenerate
`endif
// }}}
endmodule
