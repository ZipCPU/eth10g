////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/axishdmi.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generates the timing signals (not the clock) for an outgoing
//		video signal, and then encodes the incoming pixels into
//	an HDMI data stream.
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
`default_nettype	none
// }}}
module	axishdmi #(
		// {{{
		parameter	HW=12,
				VW=12,
		parameter [0:0]	OPT_RESYNC_ON_VLAST = 1'b0,
		parameter [0:0]	OPT_DATAISLAND = 1'b1,
		// HDMI *only* works with 24-bit color, using 8-bits per color
		localparam	BITS_PER_COLOR = 8,
		localparam	BPC = BITS_PER_COLOR,
				BITS_PER_PIXEL = 3 * BPC,
				BPP = BITS_PER_PIXEL
		// }}}
	) (
		// {{{
		input	wire	i_pixclk,
		// Verilator lint_off SYNCASYNCNET
		input	wire			i_reset,
		// Verilator lint_on SYNCASYNCNET
		//
		// AXI Stream packet interface
		// {{{
		input	wire		i_pkt_valid,
		output	wire		o_pkt_ready,
		input	wire		i_pkt_hdr,
		input	wire [7:0]	i_pkt_data,
		input	wire		i_pkt_last,
		// }}}
		//
		// AXI Stream video interface
		// {{{
		input	wire		i_valid,
		output	reg		o_ready,
		input	wire		i_hlast,
		input	wire		i_vlast,
		input	wire [BPP-1:0]	i_rgb_pix,
		// }}}
		//
		// Video mode information
		// {{{
		input	wire [HW-1:0]	i_hm_width,
		input	wire [HW-1:0]	i_hm_porch,
		input	wire [HW-1:0]	i_hm_synch,
		input	wire [HW-1:0]	i_hm_raw,
		input	wire 		i_hm_syncpol,
		//
		input	wire [VW-1:0]	i_vm_height,
		input	wire [VW-1:0]	i_vm_porch,
		input	wire [VW-1:0]	i_vm_synch,
		input	wire [VW-1:0]	i_vm_raw,
		input	wire 		i_vm_syncpol,
		// }}}
		//
		// HDMI outputs
		// {{{
		output	wire	[9:0]	o_red,
		output	wire	[9:0]	o_grn,
		output	wire	[9:0]	o_blu
		// }}}
		// }}}
	);

	// Register declarations
	// {{{
	localparam	[1:0]	GUARD = 2'b00,
				CTL_PERIOD  = 2'b01,
				DATA_ISLAND = 2'b10,
				VIDEO_DATA  = 2'b11;
	localparam		GUARD_PIXELS= 2;

	reg		r_newline, r_newframe, lost_sync;
	reg		vsync, hsync, vblank, vlast;
	reg		hdmi_gtype;	// Type of guard pixel, 0 = video guard
	reg	[1:0]	hdmi_type;
	reg	[3:0]	hdmi_ctl;
	reg	[11:0]	hdmi_data;
	reg	[7:0]	red_pixel, grn_pixel, blu_pixel;
	reg		pre_line;
	reg		first_frame;

	wire			w_rd;
	wire	[BPC-1:0]	i_red, i_grn, i_blu;
	assign	i_red = i_rgb_pix[3*BPC-1:2*BPC];
	assign	i_grn = i_rgb_pix[2*BPC-1:  BPC];
	assign	i_blu = i_rgb_pix[  BPC-1:0];

	reg	[HW-1:0]	hpos;
	reg	[VW-1:0]	vpos;
	reg			hrd, vrd;
	reg		pix_reset;
	reg	[1:0]	pix_reset_pipe;
	wire		w_external_sync;
`ifdef	FORMAL
	wire	[47:0]		f_vmode, f_hmode;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronize the reset release
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	{ pix_reset, pix_reset_pipe } = -1;
	always @(posedge i_pixclk, posedge i_reset)
	if (i_reset)
		{ pix_reset, pix_reset_pipe } <= -1;
	else
		{ pix_reset, pix_reset_pipe } <= { pix_reset_pipe, 1'b0 };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Horizontal line counting
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// hpos, r_newline, hsync, hrd
	// {{{
	initial	hpos       = 0;
	initial	r_newline  = 0;
	initial	hsync = 0;
	initial	hrd = 1;
	always @(posedge i_pixclk)
	if (pix_reset)
	begin
		// {{{
		hpos <= 0;
		r_newline <= 1'b0;
		hsync <= 1'b0;
		hrd <= 1;
		// }}}
	end else if (w_external_sync)
	begin
		hpos      <= i_hm_width-1;
		r_newline <= 0;
		hrd       <= 0;
		hsync <= 1'b0;
	end else begin
		// {{{
		hrd <= (hpos < i_hm_width-2)
				||(hpos >= i_hm_raw-2);
		if (hpos < i_hm_raw-1'b1)
			hpos <= hpos + 1'b1;
		else
			hpos <= 0;
		r_newline <= (hpos == i_hm_width-3);
		hsync <= (hpos >= i_hm_porch-1'b1)&&(hpos<i_hm_synch-1'b1);
		// }}}
	end
	// }}}

	// lost_sync detection
	// {{{
	assign	w_external_sync = (OPT_RESYNC_ON_VLAST && i_valid && o_ready
			&& i_vlast && i_hlast);

	initial	lost_sync = 1;
	always @(posedge i_pixclk)
	if (pix_reset)
		lost_sync <= 1;
	else if (w_external_sync)
		lost_sync <= 0;
	else if (w_rd)
	begin
		if (r_newframe && i_hlast && i_vlast && i_valid)
			lost_sync <= 0;
		else begin
			if (!i_valid)
				lost_sync <= 1;
			if (i_hlast != r_newline)
				lost_sync <= 1;
			if ((i_vlast && i_hlast) != r_newframe)
				lost_sync <= 1;
		end
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Vertical / frame based timing and synchronization
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_newframe
	// {{{
	initial	r_newframe = 0;
	always @(posedge i_pixclk)
	if (pix_reset)
		r_newframe <= 1'b0;
	else if (w_external_sync)
		r_newframe <= 1'b0;
	else if ((hpos == i_hm_width - 3)&&(vpos == i_vm_height-1))
		r_newframe <= 1'b1;
	else
		r_newframe <= 1'b0;
	// }}}

	// vblank
	// {{{
	always @(posedge i_pixclk)
	if (i_reset || lost_sync)
		vblank <= 1'b0;
	else if (w_external_sync)
		vblank <= 1'b1;
	else if (vpos > 0 && vpos < i_vm_height-1)
		vblank <= 1'b0;
	else if (vpos == 0 && hpos < i_hm_width)
		vblank <= 1'b0;
	else if (vpos == 0 && hpos >= i_hm_raw-1)
		vblank <= 1'b0;
	else if (hpos >= i_hm_width)
		vblank <= 1'b1;
	// }}}

	// vlast
	// {{{
	always @(posedge i_pixclk)
	if (i_reset || lost_sync)
		vlast <= 1'b0;
	else if (w_external_sync)
		vlast <= 1'b1;
	else if (hpos == i_hm_raw-1)
		vlast <= (vpos >= i_vm_raw-1);
	// }}}

	// vpos, vsync
	// {{{
	initial	vpos = 0;
	initial	vsync = 1'b0;
	always @(posedge i_pixclk)
	if (pix_reset)
	begin
		vpos <= 0;
		vsync <= 1'b0;
	end else if (w_external_sync)
	begin
		vpos  <= i_vm_height -1;
		vsync <= 0;
	end else if (hpos == i_hm_porch-1'b1)
	begin
		if (vpos < i_vm_raw-1'b1)
			vpos <= vpos + 1'b1;
		else
			vpos <= 0;
		// Realistically, the new frame begins at the top
		// of the next frame.  Here, we define it as the end
		// last valid row.  That gives any software depending
		// upon this the entire time of the front and back
		// porches, together with the synch pulse width time,
		// to prepare to actually draw on this new frame before
		// the first pixel clock is valid.
		vsync <= (vpos >= i_vm_porch-1'b1)&&(vpos<i_vm_synch-1'b1);
	end
	// }}}

	// vrd
	// {{{
	initial	vrd = 1'b1;
	always @(posedge i_pixclk)
		vrd <= (vpos < i_vm_height)&&(!pix_reset);
	// }}}

	// first_frame
	// {{{
	initial	first_frame = 1'b1;
	always @(posedge i_pixclk)
	if (pix_reset)
		first_frame <= 1'b1;
	else if (OPT_RESYNC_ON_VLAST && w_external_sync)
		first_frame <= 1'b0;
	else if (!OPT_RESYNC_ON_VLAST && r_newframe)
		first_frame <= 1'b0;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-stream Ready generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	// w_rd
	// {{{
	assign	w_rd = (hrd)&&(vrd)&&(!first_frame);
	// }}}

	// o_ready
	// {{{
	// If we've lost sync, flush the incoming frame and then force the
	// input to wait until the first of the frame.
	always @(*)
	if (lost_sync)
	begin
		if (OPT_RESYNC_ON_VLAST)
			o_ready = 1'b1;
		else if (!i_vlast || !i_hlast)
			// Skip to the end of the incoming frame before
			// trying again
			o_ready = 1'b1;
		else if (!r_newframe)
			o_ready = 1'b0;
		else
			// First pixel of a new frame--sync to it
			o_ready = 1'b1;
	end else
		o_ready = w_rd;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Data Island pre-encoding
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire		di_active;
	wire	[1:0]	di_type;

	generate if (OPT_DATAISLAND)
	begin : GEN_DATAISLAND
		localparam	[2:0]	DI_IDLE       = 0,
					DI_PREFIX     = 1,
					DI_PREGUARD   = 2,
					DI_DATA       = 3,
					DI_POSTGUARD  = 4,
					DI_FINALGUARD = 5;
		// A small state machine to guarantee proper data island
		// formatting
		reg		di_may_commit, r_active;
		reg	[2:0]	di_fsm;
		reg	[4:0]	di_counter;
		reg	[1:0]	r_type;

		// di_may_commit
		// {{{
		//	A commitment to a new data island will require
		//		12 control clocks
		//		 2 guard clocks
		//		32 data island clocks
		//		 2 guard clocks
		//	before we can return to video control pixels.  We'll
		//	then need either ...
		//		12 video control clocks
		//		 2 guard pixels
		//	before any new line (guarantees minimum duration control
		//	period), or
		//		32 video control clocks
		//		 2 guard pixels
		//	before any new frame (guarantees minimum duration
		//	_extended_ control period).
		//
		//	A. If we are not in an Island, then we can only start if
		//		there's room for
		//			(RAW_WIDTH - (12+2)-(12+2+2+32))
		//		pixels before the end of the line,
		//	    *AND* there's at least
		//			(RAW_WIDTH-(32+2)-(12+2+2+32))
		//		pixels before the end of the frame
		//	B. If we are in an island, then we can only continue if
		//		there's room for
		//			(RAW_WIDTH-(12+2)-(2+32)
		//		pixels before the end of the line, *AND*
		//		there's at least
		//			(RAW_WIDTH-(32+2)-(2+32))
		//		pixels before the end of the frame
		always @(posedge i_pixclk)
		if (i_reset)
			di_may_commit <= 0;
		else if (lost_sync)
			di_may_commit <= 0;
		else if (vblank && !vlast)
			di_may_commit <= 1;
		else if (di_active)
		begin
			// {{{
			if (!vblank)
			begin
				if (hpos + (12+2+2+32) >= i_hm_raw)
					di_may_commit <= 0;
				else
					di_may_commit <= 1;
			end else // if (vlast)
			begin
				if (hpos + (32+2+2+32) >= i_hm_raw)
					di_may_commit <= 0;
				else
					di_may_commit <= 1;
			end
			// }}}
		end else if (!vblank)
		begin
			if (hpos < i_hm_width+11)
				di_may_commit <= 0;
			else if (hpos + (12+2+12+2+2+32) >= i_hm_raw)
				di_may_commit <= 0;
			else
				di_may_commit <= 1;
		end else // if (vlast)
		begin
			if (hpos + (32+2+12+2+2+32) >= i_hm_raw)
				di_may_commit <= 0;
			else
				di_may_commit <= 1;
		end
		// }}}

		// di_active
		// {{{
		always @(posedge i_pixclk)
		if (i_reset || o_ready || lost_sync)
			r_active <= 1'b0;
		else if (di_may_commit && i_pkt_valid)
			r_active <= 1'b1;
		else if (di_fsm == DI_FINALGUARD || di_fsm == DI_IDLE)
			r_active <= 1'b0;

		assign	di_active = r_active;
		// }}}

		// di_fsm
		// {{{
		always @(posedge i_pixclk)
		if (i_reset || lost_sync)
		begin
			di_fsm <= DI_IDLE;
			di_counter <= 0;
		end else if (!di_active)
		begin
			di_fsm <= (i_pkt_valid && di_may_commit)
						? DI_PREFIX : DI_IDLE;
			di_counter <= 0;
		end else case(di_fsm)
		DI_PREFIX: begin
			di_counter <= di_counter + 1;
			if (di_counter >= 12)
				di_fsm <= DI_PREGUARD;
			end
		DI_PREGUARD: begin
			di_counter <= di_counter + 1;
			if (di_counter >= 14)
			begin
				di_fsm <= DI_DATA;
				di_counter <= 0;
			end end
		DI_DATA: begin
			di_counter <= di_counter + 1;
			if (di_counter == 31)
				di_fsm <= DI_POSTGUARD;
			end
		DI_POSTGUARD:
			di_fsm <= DI_FINALGUARD;
		DI_FINALGUARD: begin
			di_counter <= 0;
			if (i_pkt_valid && di_may_commit && !lost_sync)
			begin
				di_fsm <= DI_DATA;
			end else
				di_fsm <= DI_IDLE;
			end
		default: begin
			di_fsm <= DI_IDLE;
			di_counter <= 0;
			end // includes DI_IDLE
		endcase
		// }}}

		// di_type
		// {{{
		always @(*)
		case(di_fsm)
		DI_IDLE:	r_type = CTL_PERIOD;
		DI_PREFIX:	r_type = CTL_PERIOD;
		DI_PREGUARD:	r_type = GUARD;
		DI_DATA:	r_type = DATA_ISLAND;
		DI_POSTGUARD:	r_type = GUARD;
		DI_FINALGUARD:	r_type = GUARD;
		default:	r_type = CTL_PERIOD;
		endcase

		assign	di_type = r_type;
		// }}}

		assign	o_pkt_ready = (hdmi_type == DATA_ISLAND);
	end else begin : NO_DATAISLAND
		assign	o_pkt_ready = 1'b1;
		assign	di_type = CTL_PERIOD;
		assign	di_active = 1'b0;

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_di;
		assign	unused_di = &{ 1'b0, i_pkt_valid, i_pkt_hdr,
					i_pkt_data, i_pkt_last, vblank, vlast };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// HDMI encoding
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	// Set *_pixel values
	// {{{
	always @(posedge i_pixclk)
	if (w_rd)
	begin
		if (lost_sync)
		begin
			red_pixel <= 0;
			grn_pixel <= 0;
			blu_pixel <= 0;
		end else begin
			red_pixel <= i_red;
			grn_pixel <= i_grn;
			blu_pixel <= i_blu;
		end
	end else begin
		red_pixel <= 0;
		grn_pixel <= 0;
		blu_pixel <= 0;
	end
	// }}}

	// hdmi_type
	// {{{
	initial	pre_line = 1'b1;
	always @(posedge i_pixclk)
	if (pix_reset)
		pre_line <= 1'b1;
	else
		pre_line <= (vpos < i_vm_height);

	initial	hdmi_type = GUARD;
	always @(posedge i_pixclk)
	if (pix_reset)
	begin
		hdmi_gtype <= 1'b0;
		hdmi_type  <= GUARD;
		hdmi_ctl   <= 4'h1;
	end else if (di_active)
	begin
		hdmi_gtype <= 1'b1;
		hdmi_type  <= di_type;
		hdmi_ctl   <= 4'h5;
	end else if (pre_line)
	begin
		hdmi_ctl   <= 4'h1;
		hdmi_gtype <= 1'b0;
		if (hpos >= i_hm_raw - 1)
			hdmi_type <= VIDEO_DATA;
		else if (hpos < i_hm_width - 1)
			hdmi_type <= VIDEO_DATA;
		else if (hpos >= i_hm_raw - 1-GUARD_PIXELS)
			hdmi_type <= GUARD;
		else if (hdmi_type == DATA_ISLAND && i_pkt_valid)
		begin
			if (i_pkt_last)
				hdmi_type <= GUARD;
		end else
			hdmi_type <= CTL_PERIOD;
	end else begin
		hdmi_gtype <= 1'b0;
		hdmi_type <= CTL_PERIOD;
		hdmi_ctl   <= 4'h1;
	end
	// }}}

	// hdmi_data
	// {{{
	wire	[1:0]	sync_data;
	reg		di_pktsync;
	assign		sync_data = { vsync ^ i_vm_syncpol,
					hsync ^ i_hm_syncpol };
	always @(posedge i_pixclk)
		di_pktsync <= i_pkt_valid && o_pkt_ready;

	always @(*)
	begin
		hdmi_data[1:0]	= sync_data;
		hdmi_data[11:2] = 0;

		if (hdmi_type == DATA_ISLAND)
		begin
			hdmi_data[   2] = i_pkt_hdr;
			hdmi_data[   3] = di_pktsync;
			hdmi_data[ 7:4] = i_pkt_data[3:0];
			hdmi_data[11:8] = i_pkt_data[7:4];
		end else if (hdmi_gtype && hdmi_type == GUARD)
			hdmi_data[3:2] = 2'b11;
	end
	// }}}

	// TMDS encoding
	// {{{
`ifdef	FORMAL
	(* anyseq *) reg [9:0]	w_blu, w_grn, w_red;
	//
	// Verific complains of logic loops within tmdsencode.  Since the TMDS
	// encoder isn't really a part of our formal proof, we can cut it out
	// here and replace it's results with ... whatever we want ... just to
	// get the proof to pass.
	//

	assign	o_red = w_red;
	assign	o_grn = w_grn;
	assign	o_blu = w_blu;
`else
	// Channel 0 = blue
	tmdsencode #(
		.CHANNEL(2'b00)
	) hdmi_encoder_ch0(
		// {{{
		.i_clk(i_pixclk),
		.i_gtype(hdmi_gtype),
		.i_dtype((hdmi_gtype && hdmi_type == GUARD)
				? DATA_ISLAND : hdmi_type), .i_ctl(sync_data),
		.i_aux(hdmi_data[3:0]), .i_data(blu_pixel), .o_word(o_blu)
		// }}}
	);

	// Channel 1 = green
	tmdsencode #(
		.CHANNEL(2'b01)
	) hdmi_encoder_ch1(
		// {{{
		.i_clk(i_pixclk),
		.i_gtype(hdmi_gtype), .i_dtype(hdmi_type), .i_ctl(hdmi_ctl[1:0]),
		.i_aux(hdmi_data[7:4]),
		.i_data(grn_pixel),
		.o_word(o_grn)
		// }}}
	);

	// Channel 2 = red
	tmdsencode #(
		.CHANNEL(2'b10)
	) hdmi_encoder_ch2(
		// {{{
		.i_clk(i_pixclk),
		.i_gtype(hdmi_gtype), .i_dtype(hdmi_type), .i_ctl(hdmi_ctl[3:2]),
		.i_aux(hdmi_data[11:8]),
		.i_data(red_pixel),
		.o_word(o_red)
		// }}}
	);
`endif
	// }}}

	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties for verification purposes
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	[1:0]	DATA_ISLAND = 2'b10;
	localparam		PREGUARD_CONTROL = 6;
	reg	f_past_valid;
	reg	[47:0]	f_last_vmode, f_last_hmode;
	reg	f_stable_mode;
	reg	[3:0]	f_ctrl_length;
	reg	[1:0]	f_video_start, f_packet_start;

	////////////////////////////////////////////////////////////////////////
	//
	// Reset assumptions
	//
	initial	f_past_valid = 1'b0;
	always @(posedge i_pixclk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// AXI Stream assumptions
	//
	always @(posedge i_pixclk)
	if (f_past_valid && !$past(pix_reset))
	begin
		if ($past(i_valid && !o_ready))
		begin
			assume(i_valid);
			assume($stable(i_hlast));
			assume($stable(i_vlast));
			assume($stable(i_rgb_pix));
		end
	end

	generate if (OPT_RESYNC_ON_VLAST)
	begin : GEN_VIDCHECK
		// {{{
		localparam LGFRAME = (HW > VW) ? HW : VW;
		wire			f_vlast, f_hlast, f_sof, f_known_height;
		wire	[LGFRAME-1:0]	f_xpos, f_ypos;
		reg	[LGFRAME-1:0]	f_width, f_height;

		always @(posedge i_pixclk)
		if (!pix_reset && $past(pix_reset))
			assume(!i_valid);

		always @(*)
		begin
			f_width = 0; f_height = 0;
			f_width[HW-1:0]  = i_hm_width;
			f_height[VW-1:0] = i_vm_height;
		end

		faxivideo #(
			// {{{
			.LGDIM(LGFRAME), .PW(BPP), .OPT_TUSER_IS_SOF(1'b0),
			.OPT_SOURCE(1'b0)
			// }}}
		) fvid (
			// {{{
			.i_clk(i_pixclk), .i_reset_n(!pix_reset),
			//
			.S_VID_TVALID(i_valid && !lost_sync), .S_VID_TREADY(o_ready),
			.S_VID_TDATA(i_rgb_pix),.S_VID_TLAST(i_hlast&& i_vlast),
			.S_VID_TUSER(i_hlast),
			.i_width(f_width), .i_height(f_height),
			.o_xpos(f_xpos), .o_ypos(f_ypos),
				.f_known_height(f_known_height),
			.o_hlast(f_hlast), .o_vlast(f_vlast), .o_sof(f_sof)
			// }}}
		);

		always @(posedge i_pixclk)
		if (!i_reset && !lost_sync)
		begin
			if (w_rd)
				assume(i_valid);

			if (f_xpos != 0)
			begin
				assert(hpos == f_xpos - 1);
				assert(vpos == f_ypos);
			end else begin
				assert(hpos <= 1 || hpos >= f_width-1
					|| vpos >= i_vm_height);
				if (hpos < i_hm_width)
				begin
					assert(hpos == i_hm_width-1
						|| vpos == f_ypos
						|| (f_ypos == 0 && vpos >= f_height));
				end else if (hpos < i_hm_porch)
				begin
					if (vpos < f_height-1)
					begin
						assert(vpos + 1== f_ypos);
					end else begin
						assert(f_ypos == 0);
					end
				end else begin
					if (vpos <= f_height-1)
					begin
						assert(vpos == f_ypos);
					end else begin
						assert(f_ypos == 0);
					end
				end
			end

			if (f_ypos != 0)
			begin
			end else
				assert(vpos == 0 || vpos >= f_height -1);
		end else if (!i_reset)
		begin
			assert(f_xpos == 0);
			assert(f_ypos == 0);
		end

		always @(posedge i_pixclk)
		if (!i_reset && first_frame)
		begin
			assert(lost_sync);
			assert(!f_known_height);
			assert(f_xpos == 0);
			assert(f_ypos == 0);
		end

		always @(*)
			assume(i_hlast == f_hlast);

		always @(*)
		if (!f_vlast)
			assume(!i_vlast);
		else if (f_hlast)
			assume(i_vlast == f_hlast);
		// }}}
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Mode-line assumptions
	//
	always @(*)
	begin
		assume(12'h10 < i_hm_width);
		assume(i_hm_width < i_hm_porch);
		assume(i_hm_porch < i_hm_synch);
		assume(i_hm_synch < i_hm_raw);
		assume(i_hm_porch+14 < i_hm_raw);

		assume(12'h10 < i_vm_height);
		assume(i_vm_height < i_vm_porch);
		assume(i_vm_porch  < i_vm_synch);
		assume(i_vm_synch  < i_vm_raw);
	end

	assign	f_hmode = { i_hm_width,  i_hm_porch, i_hm_synch, i_hm_raw };
	assign	f_vmode = { i_vm_height, i_vm_porch, i_vm_synch, i_vm_raw };

	always @(posedge i_pixclk)
		f_last_vmode <= f_vmode;
	always @(posedge i_pixclk)
		f_last_hmode <= f_hmode;

	always @(*)
		f_stable_mode = (f_last_vmode == f_vmode)&&(f_last_hmode == f_hmode);

	always @(*)
	if (!pix_reset)
		assume(f_stable_mode);

	////////////////////////////////////////////////////////////////////////
	//
	// Pixel counting
	//

	always @(posedge i_pixclk)
	if ((!f_past_valid)||($past(pix_reset)))
	begin
		assert(hpos == 0);
		assert(vpos == 0);
		assert(first_frame);
	end

	always @(posedge i_pixclk)
	if ((f_past_valid)&&(!$past(pix_reset))&&(!pix_reset)
			&&(f_stable_mode)&&($past(f_stable_mode)))
	begin
		if ($past(w_external_sync))
		begin
			assert(hpos == i_hm_width);
		end else if ($past(hpos >= i_hm_raw-1'b1))
		begin
			assert(hpos == 0);
		end else
			// The horizontal position counter should increment
			assert(hpos == $past(hpos)+1'b1);

		// The vertical position counter should increment
		if ($past(w_external_sync))
		begin
		end else if (hpos == i_hm_porch)
		begin
			if ($past(vpos >= i_vm_raw-1'b1))
			begin
				assert(vpos == 0);
			end else
				assert(vpos == $past(vpos)+1'b1);
		end else
			assert(vpos == $past(vpos));

		// For induction purposes, we need to insist that both
		// horizontal and vertical counters stay within their
		// required ranges
		assert(hpos < i_hm_raw);
		assert(vpos < i_vm_raw);

		// If we are less than the data width for both horizontal
		// and vertical, then we should be asserting we are in a
		// valid data cycle
		// if ((hpos < i_hm_width)&&(vpos < i_vm_height)
		//		&&(!first_frame))
		//	assert(w_rd);
		// else
		//	assert(!w_rd);

		//
		// The horizontal sync should only be valid between positions
		// i_hm_porch <= hpos < i_hm_sync, invalid at all other times
		//
		if (hpos < i_hm_porch)
		begin
			assert(!hsync);
		end else if (hpos < i_hm_synch)
		begin
			assert(hsync);
		end else
			assert(!hsync);

		// Same thing for vertical
		if (vpos < i_vm_porch)
		begin
			assert(!vsync);
		end else if (vpos < i_vm_synch)
		begin
			assert(vsync);
		end else
			assert(!vsync);

		// At the end of every horizontal line cycle, we assert
		// a new line
		if (hpos == i_hm_width-2)
		begin
			assert(r_newline);
		end else
			assert(!r_newline);

		// At the end of every vertical frame cycle, we assert
		// a new frame, but only on the newline measure
		if ((vpos == i_vm_height-1'b1)&&(r_newline))
		begin
			assert(r_newframe);
		end else
			assert(!r_newframe);
	end

	//////////////////////////////
	//
	// HDMI Specific properties
	//
	//////////////////////////////

	always @(posedge i_pixclk)
	if (pix_reset)
		f_ctrl_length <= 4'hf;
	else if (hdmi_type != CTL_PERIOD)
		f_ctrl_length <= 0;
	else if (f_ctrl_length < 4'hf)
		f_ctrl_length <= f_ctrl_length + 1'b1;

	initial	f_video_start = 2'b01;
	always @(posedge i_pixclk)
	if (pix_reset)
		f_video_start = 2'b01;
	else if ((f_video_start == 2'b00)
			&&(f_ctrl_length >= 4'hc)&&(hdmi_type == GUARD)
			&&(hdmi_ctl == 4'h1))
		f_video_start <= 2'b1;
	else if ((f_video_start == 2'b01)&&(hdmi_type == GUARD)
			&&(hdmi_ctl == 4'h1))
		f_video_start <= 2'b10;
	else
		f_video_start <= 2'b00;

	always @(posedge i_pixclk)
	if ((f_ctrl_length >= 4'hc)&&(hdmi_type == GUARD))
		f_packet_start <= 2'b1;
	else if ((f_packet_start == 2'b1)&&(hdmi_type == GUARD))
		f_packet_start <= 2'b10;
	else
		f_packet_start <= 2'b00;

	always @(posedge i_pixclk)
	if ((f_past_valid)&&(!$past(pix_reset)))
	begin
		if (($past(hdmi_type != VIDEO_DATA))
				&&(f_video_start != 2'b10))
			assert(hdmi_type != VIDEO_DATA);
	end

	always @(posedge i_pixclk)
	if ((f_past_valid)&&(!$past(pix_reset))&&(!pix_reset))
	begin
		if ($past(w_external_sync))
		begin
		end else if ((hpos < i_hm_width)&&(vpos < i_vm_height))
		begin
			assert(hdmi_type == VIDEO_DATA);
		end else
			assert(hdmi_type != VIDEO_DATA);
		if (!$past(first_frame))
			assert($past(w_rd) == (hdmi_type == VIDEO_DATA));

		if (vpos < i_vm_height)
		begin
			if (hpos < i_hm_width)
				assert(hdmi_type == VIDEO_DATA);
			if (hpos >= (i_hm_raw-GUARD_PIXELS))
			begin
				assert(hdmi_type == GUARD);
			end else if (hpos >= (i_hm_raw-GUARD_PIXELS-PREGUARD_CONTROL))
				assert((hdmi_type == CTL_PERIOD)
					&&(hdmi_ctl == 4'h1));
		end
	end

	// always @(posedge i_pixclk)
	// if ((f_past_valid)&&(!$past(i_reset)))
		// assert(o_rd == (hdmi_type == VIDEO_DATA));

`ifdef	VERIFIC
	// {{{
	sequence	VIDEO_PREAMBLE;
		(hdmi_type == CTL_PERIOD) [*2]
		##1 ((hdmi_type == CTL_PERIOD)&&(hdmi_ctl == 4'h1)) [*10]
		##1 (hdmi_type == GUARD) [*2];
	endsequence

	assume property (@(posedge i_pixclk)
		VIDEO_PREAMBLE
		|=> (hdmi_type == VIDEO_DATA)&&(hpos == 0)&&(vpos == 0));

	// assert property (@(posedge i_pixclk)
	//	disable iff (pix_reset)
	//	((hdmi_type != VIDEO_DATA) throughout (not VIDEO_PREAMBLE)));

	//
	// Data Islands
	//
	sequence	DATA_PREAMBLE;
		(hdmi_type == CTL_PERIOD) [*2]
		##1 ((hdmi_type == CTL_PERIOD)&&(hdmi_ctl == 4'h5)) [*10]
		##1 (hdmi_type == GUARD) [*2];
	endsequence

	assert property (@(posedge i_pixclk)
		disable iff (pix_reset)
		(DATA_PREAMBLE)
		|=> 0 && (hdmi_type == DATA_ISLAND)[*64]
		##1 0 && (hdmi_type == GUARD) [*2]);

	// assert property (@(posedge i_pixclk)
	//	disable iff (pix_reset)
	//	((hdmi_type != DATA_ISLAND) throughout (not DATA_PREAMBLE))
	//	|=> (hdmi_type != DATA_ISLAND));

	// }}}
`endif
`endif
// }}}
endmodule
