////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/hdmi2vga.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Convert an HDMI input stream into an outgoing VGA stream,
//		for further processing as a (nearly video format independent)
//	stream.
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
//
`default_nettype	none
// }}}
module	hdmi2vga #(
		parameter [0:0] OPT_DATAISLAND = 1'b1
	) (
		// {{{
		input	wire		i_clk,	i_reset,
		input	wire	[9:0]	i_hdmi_red,
		input	wire	[9:0]	i_hdmi_grn,
		input	wire	[9:0]	i_hdmi_blu,
		//
		output	reg		o_pix_valid,
		output	reg		o_vsync,
		output	reg		o_hsync,
		output	reg	[7:0]	o_vga_red, o_vga_green, o_vga_blue,
		//
		output	wire		M_DI_VALID,
		output	wire		M_DI_HDR,
		output	wire	[7:0]	M_DI_DATA,
		output	wire		M_DI_LAST,
		//
		output	wire	[31:0]	o_sync_word,
		output	reg	[31:0]	o_debug
		// }}}
	);

	// Register/wire definitions
	// {{{
	wire	[9:0]	blu_word, grn_word, red_word;
	// Decoded data, not yet word synchronized
	wire	[1:0]	ublu_ctl, ugrn_ctl, ured_ctl;
	wire	[6:0]	ublu_aux, ugrn_aux, ured_aux;
	wire	[7:0]	ublu_pix, ugrn_pix, ured_pix;
	// now synchronized word dsata
	reg	[1:0]	sblu_ctl, sgrn_ctl, sred_ctl;
	reg	[6:0]	sblu_aux, sgrn_aux, sred_aux;
	reg	[7:0]	sblu_pix, sgrn_pix, sred_pix;

	reg	[8:0]	video_control_blu, video_control_grn, video_control_red;
	reg		video_guard_blu, video_guard_grn, video_guard_red;
	reg	[2:0]	video_start_blu, video_start_grn, video_start_red;
	reg		video_start, video_period;
	reg		pre_video_start_blu, pre_video_start_grn,
			pre_video_start_red;

	reg	[1:0]	lag_blu, lag_red, lag_grn;
	reg	[33:0]	lag_data_blu, lag_data_red, lag_data_grn;

	reg		non_video_data, control_sync;
	reg	[10:0]	control_sync_sreg;

	reg		r_pix_valid;
	reg	[7:0]	r_vga_red, r_vga_green, r_vga_blue;

	wire	[31:0]	dbg_bitsync, dbg_vga;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bit synchronization: [clr]_word and sync_word generation
	// {{{
`ifndef	FORMAL
	hdmibitsync
	bitsync(
		.i_pix_clk(i_clk), .i_reset(i_reset),
		.i_r(i_hdmi_red), .i_g(i_hdmi_grn), .i_b(i_hdmi_blu),
		.o_r(red_word), .o_g(grn_word), .o_b(blu_word),
		.o_sync_word(o_sync_word),
		.o_debug(dbg_bitsync)
	);
`else
	assign	red_word = i_hdmi_red;
	assign	grn_word = i_hdmi_grn;
	assign	blu_word = i_hdmi_blu;
	assign	o_sync_word = 32'h0;
	assign	dbg_bitsync = 32'h0;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// TMDS decoding
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	tmdsdecode
	decblu(i_clk, blu_word, ublu_ctl, ublu_aux, ublu_pix);

	tmdsdecode
	decgrn(i_clk, grn_word, ugrn_ctl, ugrn_aux, ugrn_pix);

	tmdsdecode
	decred(i_clk, red_word, ured_ctl, ured_aux, ured_pix);


// ifdef	FORMAL
//	We assume the tmdsdecode works, and start with making assumptions about
//	the outputs of the tmds decoder.
// endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video data start detection, and channel sync
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Synchronization requires:
	//	12 (or more) control characters (minimum duration)
	//	32 (or more) control characters at least once every 50ms
	//
	// Video data begins with:
	// 	1. 8x (or more) video data preamble (control) characters
	//	2. 2x video Guard character(s)
	//		BLU = 10_1100_1100 = 10'h2cc
	//		GRN = 01_0011_0011 = 10'h133
	//		RED = 10_1100_1100 = 10'h2cc
	//

	// video_control_blu, video_guard_blu => video_start_blu
	// {{{
	initial	video_control_blu = 0;
	always @(posedge i_clk)
		video_control_blu <= {video_control_blu[7:0], ublu_aux[4] };

	initial	video_guard_blu = 0;
	always @(posedge i_clk)
		video_guard_blu <= ublu_aux[6] && !ublu_aux[0];

	always @(*)
		// Start = 8 control bits followed by two guard bits
		pre_video_start_blu = (&video_control_blu[8:1])
				&& video_guard_blu
				&& ublu_aux[6] && !ublu_aux[0];

	initial	video_start_blu = 0;
	always @(posedge i_clk)
		video_start_blu <= { video_start_blu[1:0], pre_video_start_blu};
	// }}}

	// video_control_grn, video_guard_grn => video_start_grn
	// {{{
	initial	video_control_grn = 0;
	always @(posedge i_clk)
		video_control_grn <= {video_control_grn[7:0],
				// Video data periods start with
				// {CTL1,CTL0} == 2'b01
				ugrn_aux[4] && ugrn_ctl == 2'b01 };

	initial	video_guard_grn = 0;
	always @(posedge i_clk)
		video_guard_grn <= ugrn_aux[6] && ugrn_aux[0];

	always @(*)
		pre_video_start_grn = (&video_control_grn[8:1])
				&&(video_guard_grn)
				&& ugrn_aux[6] && ugrn_aux[0];

	initial	video_start_grn = 0;
	always @(posedge i_clk)
		video_start_grn <= { video_start_grn[1:0],
			pre_video_start_grn };
	// }}}

	// video_control_red, video_guard_red => video_start_red
	// {{{
	initial	video_control_red = 0;
	always @(posedge i_clk)
		video_control_red <= {video_control_red[7:0],
				// Video data periods start with
				// {CTL3,CTL2} == 2'b00
				ured_aux[4] && ured_ctl == 2'b00 };

	initial	video_guard_red = 0;
	always @(posedge i_clk)
		video_guard_red <= ured_aux[6] && !ured_aux[0];

	always @(*)
		pre_video_start_red =
			(&video_control_red[8:1])&&(video_guard_red)
			&& ured_aux[6] && !ured_aux[0];

	initial	video_start_red = 0;
	always @(posedge i_clk)
		video_start_red <= { video_start_red[1:0],
			pre_video_start_red };
			// (&video_control_red[9:2])&&(&video_guard_red) };
	// }}}

	// video_start, lag_[clr]
	// {{{
	// To be a valid start indication, we must see a start signal on
	// one frame at this time, and on all other frames in either this or
	// the last clock cycle.
	initial	video_start = 1'b0;
	always @(posedge i_clk)
		video_start <= (|{video_start_red[1:0], pre_video_start_red})
				&&(|{video_start_grn[1:0], pre_video_start_grn})
				&&(|{video_start_blu[1:0], pre_video_start_blu})
			&&(|{ pre_video_start_red, pre_video_start_grn,
							pre_video_start_blu });

	always @(posedge i_clk)
	if (video_start)
	begin
		lag_blu <= video_start_blu[2:1];
		lag_grn <= video_start_grn[2:1];
		lag_red <= video_start_red[2:1];
	end
	// }}}

	// lag_data_[clr], s[clr]_[ctl,aux,pix]: Frame sync
	// {{{
	// bit sync achieved above, now we align our various color channels.
	// We allow them to be off by only a single pixel clock.
	always @(posedge i_clk)
	begin
		lag_data_blu <= { lag_data_blu[16:0], ublu_ctl, ublu_aux, ublu_pix };
		lag_data_grn <= { lag_data_grn[16:0], ugrn_ctl, ugrn_aux, ugrn_pix };
		lag_data_red <= { lag_data_red[16:0], ured_ctl, ured_aux, ured_pix };

		if (lag_blu[0])
			{ sblu_ctl, sblu_aux, sblu_pix } <= lag_data_blu[16:0];
		else if (lag_blu[1])
			{ sblu_ctl, sblu_aux, sblu_pix } <= lag_data_blu[33:17];
		else
			{ sblu_ctl, sblu_aux, sblu_pix }
					<= { ublu_ctl, ublu_aux, ublu_pix };

		if (lag_grn[0])
			{ sgrn_ctl, sgrn_aux, sgrn_pix } <= lag_data_grn[16:0];
		else if (lag_grn[1])
			{ sgrn_ctl, sgrn_aux, sgrn_pix } <= lag_data_grn[33:17];
		else
			{ sgrn_ctl, sgrn_aux, sgrn_pix }
					<= { ugrn_ctl, ugrn_aux, ugrn_pix };

		if (lag_red[0])
			{ sred_ctl, sred_aux, sred_pix } <= lag_data_red[16:0];
		else if (lag_red[1])
			{ sred_ctl, sred_aux, sred_pix } <= lag_data_red[33:17];
		else
			{ sred_ctl, sred_aux, sred_pix }
					<= { ured_ctl, ured_aux, ured_pix };
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Data island start detection, post channel sync
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_DATAISLAND)
	begin : GEN_DATAISLAND
		// Local declarations
		// {{{
		wire		this_data_guard;
		reg		last_data_guard;
		reg	[8:0]	prime_sreg;
		reg		data_primed;
		reg		di_valid, di_last, di_hdr;
		reg	[7:0]	di_data;
		reg	[4:0]	di_pkt_count;
		// }}}

		// Notes
		// {{{
		// Data islands begin with:
		// 	1. 8x (or more) data island preamble (control) characters
		//	2. 2x Data Guard character(s)
		//		BLU	(TERC4 character, not guard)
		//		GRN	01_0011_0011 = 10'h133
		//		RED	01_0011_0011 = 10'h133
		// and ends with:
		//	1. 2x Data guard trailer
		// }}}

		// [this|last]_data_guard
		// {{{
		assign	this_data_guard = sblu_aux[5] && sblu_aux[3:2] == 2'b11
					&& sgrn_aux[6] && sgrn_aux[0]
					&& sred_aux[6] && sred_aux[0];

		initial	last_data_guard = 1'b0;
		always @(posedge i_clk)
			last_data_guard <= this_data_guard;
		// }}}

		// data_primed
		// {{{
		initial	prime_sreg  = 0;
		initial	data_primed = 1'b0;
		always @(posedge i_clk)
		begin
			data_primed <= 1'b0;
			prime_sreg <= { prime_sreg[7:0], 1'b0 };

			if (sblu_aux[4] && sgrn_aux[4] && sgrn_ctl == 2'b01
					&& sred_aux[4] && sred_ctl == 2'b01)
				prime_sreg[0] <= 1'b1;

			if (this_data_guard && last_data_guard
						&& (&prime_sreg[8:1]))
				data_primed <= 1'b1;
		end
		// }}}

		// M_DI_VALID
		// {{{
		always @(posedge i_clk)
		if (di_valid)
		begin
			di_valid <= sblu_aux[5] && sgrn_aux[5] && sred_aux[5]
				&& sblu_aux[3];
		end else if (data_primed && !di_valid)
			di_valid <= sblu_aux[5] && !sblu_aux[3]
				&& sgrn_aux[5] && sred_aux[5];

		assign	M_DI_VALID = di_valid;
		// }}}

		// M_DI_HDR, M_DI_DATA
		// {{{
		always @(posedge i_clk)
		begin
			di_hdr  <= 1;
			di_data <= 0;
			if (sblu_aux[5])
			begin
				// If blue is a control word, then it contains
				// our V & H sync channels.
				di_hdr <= sblu_aux[2];
			end

			if (sgrn_aux[5])
				di_data[3:0] <= sgrn_aux[3:0];
			if (sred_aux[5])
				di_data[7:4] <= sred_aux[3:0];
		end

		assign	M_DI_HDR  = di_hdr;
		assign	M_DI_DATA = di_data;
		// }}}

		// S_LAST
		// {{{
		always @(posedge i_clk)
		if (!di_valid || di_last)
			di_pkt_count <= 0;
		else
			di_pkt_count <= di_pkt_count + 1;

		always @(posedge i_clk)
			di_last <= di_valid && (di_pkt_count == 30);

		assign	M_DI_LAST = di_last;
		// }}}
	end else begin : NO_DATAISLAND_
		assign	M_DI_VALID = 1'b0;
		assign	M_DI_HDR   = 1'b0;
		assign	M_DI_DATA  = 8'b0;
		assign	M_DI_LAST  = 1'b0;
	end endgenerate
	// }}}

	// non_video_data
	// {{{
	// Must be combinatorial function of s[red|grn|blu]_*
	always @(*)
		// non-video data ends a stream of video pixels.  We'll assume
		// control data on all three channels marks the end of video
		// data.
		non_video_data = (sblu_aux[4])&&(sgrn_aux[4]) &&(sred_aux[4]);
	// }}}

	// control_sync
	// {{{
	// Detect a period of 12 control characters
	always @(posedge i_clk)
	begin
		control_sync_sreg[10]   <= (&control_sync_sreg[9:0])
				&& sblu_aux[4] && sgrn_aux[4] && sred_aux[4];
		control_sync_sreg[9:1] <=  control_sync_sreg[ 8:0];
		control_sync_sreg[0]    <= sblu_aux[4] && sgrn_aux[4]
							&& sred_aux[4];
	end

	always @(*)
		control_sync = control_sync_sreg[10]
				&& sred_aux[4] && sgrn_aux[4] && sblu_aux[4];
	// }}}

	// Sync period detection
	// {{{
	// *MUST* depend combinatorial on s[reg|grn|blu]_* signals, nothing
	// removed from those.  In practice, we may also depend on the
	// u[reg|grn|blu]_* signals.
	always @(posedge i_clk)
	if (control_sync)	// This is the 12th word in the sync
		video_period <= 0;
	else if (video_start)
		video_period <= 1;
	else if (non_video_data)
		video_period <= 0;
	// }}}

	// Outgoing signals
	// {{{
	// These all depend on the s[red|grn|blu]_* values.  One clock further
	// is used below to set the output.
	//
	// video_start is dependent upon the u[red|grn|blu]_* values, but
	// the values existing *before* the first video pixel--so it
	// should be synchronous with the s[red|grn|blue]_* values, only
	// the values before the video period starts.
	//
	// non_video_data is a combinatorial expression of s[red|grn|blue]_*.
	always @(posedge i_clk)
	begin
		r_pix_valid <= (video_period && !non_video_data);

		r_vga_red   <= sred_pix;
		r_vga_green <= sgrn_pix;
		r_vga_blue  <= sblu_pix;

		// AUX[6] == GUARD encoding
		// AUX[5] == TERC4 encoding
		// AUX[4] == control encoding
		if ((!sblu_aux[6] || sblu_aux[0]
					|| !sgrn_aux[6] || !sred_aux[6])
				&& (|sblu_aux[5:4])
				&& (!video_period || non_video_data))
		begin
			// If blue is either a control word or a TERC4 data
			// island packet word, then it contains our V & H sync
			// channels.  Ignore any potential video guard pixels
			o_vsync <= sblu_ctl[1];
			o_hsync <= sblu_ctl[0];
		end
	end

	always @(*)
	begin
		o_pix_valid = r_pix_valid;

		o_vga_red   = r_vga_red;
		o_vga_green = r_vga_green;
		o_vga_blue  = r_vga_blue;
	end
	// }}}

	reg	[7:0]	dbg_red, dbg_grn, dbg_blu;

	always @(*)
	begin
		if (ured_aux[6])
			// GUARD encoding
			dbg_red = { 3'b110, 4'h0, ured_aux[0] };
		else if (ured_aux[4])
			// Control encoding (will never be TERC4)
			dbg_red = { 3'b111, 3'h0, ured_ctl };
		else if (ured_aux[5])
			// TERC4 encoding
			dbg_red = { 2'b10,  2'h0, ured_aux[3:0] };
		else
			// Video pixel encoding
			dbg_red = r_vga_red;

		if (ugrn_aux[6])
			// GUARD
			dbg_grn = { 3'b110, 4'h0, ugrn_aux[0] };
		else if (ugrn_aux[4])
			// Control
			dbg_grn = { 3'b111, 3'h0, ugrn_ctl };
		else if (ugrn_aux[5])
			// TERC4
			dbg_grn = { 2'b10,  2'h0, ugrn_aux[3:0] };
		else
			// TERC4
			dbg_grn = r_vga_green;

		if (ublu_aux[6])
			// GUARD
			dbg_blu = { 3'b110, 4'h0, ublu_aux[0] };
		else if (ublu_aux[4])
			// Control
			dbg_blu = { 3'b111, 3'h0, ublu_ctl };
		else if (ublu_aux[5])
			// TERC4
			dbg_blu = { 2'b10,  2'h0, ublu_aux[3:0] };
		else
			dbg_blu = r_vga_blue;

	end

	assign	dbg_vga = { video_start, control_sync,
			video_start_red[0],
				video_start_grn[0], video_start_blu[0],
			r_pix_valid, o_vsync, o_hsync,
			dbg_red, dbg_grn, dbg_blu };

	always @(posedge i_clk)
	begin
		o_debug <= dbg_vga;
		o_debug <= 0;

		o_debug[28] <= o_pix_valid;
		o_debug[27] <= o_vsync;
		o_debug[26] <= o_hsync;
		o_debug[25:24] <= { sgrn_aux[5], sred_aux[5] };	// 2
		o_debug[23:20] <= sgrn_aux[3:0];	// 4
		o_debug[19:16] <= sred_aux[3:0];	// 4
		o_debug[15:11] <= sblu_aux[6:2];	// 5
		o_debug[ 10] <= M_DI_VALID;		// 11
		o_debug[  9] <= M_DI_HDR;
		o_debug[  8] <= M_DI_LAST;
		o_debug[7:0] <= M_DI_DATA;

		// o_debug[30:28] <=   ublu_aux[6:4];
		// o_debug[27:20] <=    dbg_blu[7:0];
		// o_debug[19:10] <=   blu_word[9:0];
		// o_debug[ 9: 0] <= i_hdmi_blu[9:0];

		// o_debug[31] <= video_start_red[0];
		// o_debug[30] <= video_start_grn[0];
		// o_debug[29:0] <= { red_word, grn_word, blu_word };
	end

	// Make verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, sblu_aux[3:0], sgrn_aux[3:0], sred_aux[3:0],
			sgrn_ctl, sred_ctl, control_sync,
			sred_aux[6:5], sgrn_aux[6:5], sblu_aux[6:5],
			dbg_bitsync, dbg_vga
			};
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
	localparam	LGDIM = 16;
	reg	f_past_valid;
	(* anyconst *)	reg	[LGDIM-1:0]	fh_width, fv_height,
						fh_front, fv_front,
						fh_sync,  fv_sync,
						fh_raw,   fv_raw;
	(* anyconst *)	reg		fh_syncpol, fv_syncpol;
	(* anyconst *)	reg	[1:0] fred_offset, fgrn_offset, fblu_offset;
	reg	[LGDIM-1:0]	f_hpos, f_vpos;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	////////////////////////////////////////////////////////////////////////
	//
	// Input assumptions
	// {{{
	always @(*)
	begin
		assume(fh_width  > 4);
		assume(fh_width  < fh_front);
		assume(fh_front  < fh_sync);
		assume(fh_sync +10 < fh_raw);

		assume(fv_height > 2);
		assume(fv_height < fv_front);
		assume(fv_front  < fv_sync);
		assume(fv_sync   < fv_raw);

		assume(fred_offset <= 2);
		assume(fgrn_offset <= 2);
		assume(fblu_offset <= 2);

		assume((fred_offset == 0)
			|| (fgrn_offset == 0)
			|| (fblu_offset == 0));
	end

	initial	f_hpos = 0;
	initial	f_vpos = 0;
	always @(posedge i_clk)
	begin
		if (f_hpos +1 >= fh_raw)
			f_hpos <= 0;
		else
			f_hpos <= f_hpos + 1;

		if (f_hpos +1 == fh_front)
		begin
			if (f_vpos + 1 >= fv_raw)
				f_vpos <= 0;
			end
				f_vpos <= f_vpos + 1;
		end
	end

	always @(*)
	begin
		if (f_hpos + fred_offset >= fh_raw)
			fred_hpos = f_hpos + fred_offset - fh_raw;
		else
			fred_hpos = f_hpos + fred_offset;

		if (f_hpos + fgrn_offset >= fh_raw)
			fgrn_hpos = f_hpos + fgrn_offset - fh_raw;
		else
			fgrn_hpos = f_hpos + fgrn_offset;

		if (f_hpos + fblu_offset >= fh_raw)
			fblu_hpos = f_hpos + fblu_offset - fh_raw;
		else
			fblu_hpos = f_hpos + fblu_offset;

		if (f_hpos + fblu_offset >= fh_front && f_hpos < fh_front)
		begin
			if (fblu_vpos + 1 < fv_raw)
				fblu_vpos = f_vpos + 1;
			else
				fblu_vpos = 0;
		end else
			fblu_vpos = f_vpos;

		if (f_hpos + fblu_offset == fh_front)
			assume(ublu_aux[4]);
		if (ublu_aux[4])
		begin
			assume(ublu_ctl[0] ^ fh_syncpol
				== ((fblu_hpos >= fh_front)&&(fblu_hpos<fh_sync)));
			assume(ublu_ctl[1] ^ fv_syncpol
				== ((fblu_vpos >= fv_front)&&(fblu_vpos<fv_sync)));
		end
	end

	always @(*)
	begin
		if (fred_hpos < fh_width)
			assume(ured_aux[6:4] == 3'h0);
		if (fgrn_hpos < fh_width)
			assume(ugrn_aux[6:4] == 3'h0);
		if (fblu_hpos < fh_width)
			assume(ublu_aux[6:4] == 3'h0);

		if (fred_hpos == fh_width) assume(ured_aux[4]);
		if (fgrn_hpos == fh_width) assume(ugrn_aux[4]);
		if (fblu_hpos == fh_width) assume(ublu_aux[4]
					&& ublu_ctl[1] == fv_syncpol
					&& ublu_ctl[0] == fh_syncpol);

		// Video starts
		// {{{
		// Control words
		if (fred_hpos + 10 >= fh_raw && fred_hpos + 2 <= fh_raw)
			assume(ured_aux[4]);

		if (fgrn_hpos + 10 >= fh_raw && fgrn_hpos + 2 <= fh_raw)
			assume(ugrn_aux[4] && ugrn_ctl == 2'b01);

		if (fgrn_hpos + 10 >= fh_raw && fgrn_hpos + 2 <= fh_raw)
			assume(ublu_aux[4]);

		// Guard words
		if (fred_hpos + 2 >= fh_raw)
			assume(ured_aux[6] && !ured_aux[0]);

		if (fgrn_hpos + 2 >= fh_raw)
			assume(ugrn_aux[6] &&  ugrn_aux[0]);

		if (fgrn_hpos + 2 >= fh_raw)
			assume(ublu_aux[6] && !ublu_aux[0]);
		// }}}

		// Data starts
		// {{{
		if (fred_hpos + 2 < fh_raw) assume(!ured_aux[6]);
		if (fgrn_hpos + 2 < fh_raw) assume(!ugrn_aux[6]);
		if (fblu_hpos + 2 < fh_raw) assume(!ublu_aux[6]);

		if (fred_hpos + 10 < fh_raw)
			assume(!ured_aux[4] || ured_ctl == 2'b00);

		/*
		// Control words
		if (fred_hpos + 10 >= fh_raw && fred_hpos + 2 <= fh_raw)
			assume(ured_aux[4]);

		if (fgrn_hpos + 10 >= fh_raw && fgrn_hpos + 2 <= fh_raw)
			assume(ugrn_aux[4] && ugrn_ctl == 2'b01);

		if (fgrn_hpos + 10 >= fh_raw && fgrn_hpos + 2 <= fh_raw)
			assume(ublu_aux[4]);

		// Guard words
		if (fred_hpos + 2 >= fh_raw)
			assume(ured_aux[6] && !ured_aux[0]);

		if (fgrn_hpos + 2 >= fh_raw)
			assume(ugrn_aux[6] &&  ugrn_aux[0]);

		if (fgrn_hpos + 2 >= fh_raw)
			assume(ublu_aux[6] && !ublu_aux[0]);
		*/
		// }}}
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output assertions
	// {{{
	always @(posedge i_clk)
	if (fred_hpos != 1)
		assert(!video_start_red);
	always @(posedge i_clk)
	if (fgrn_hpos != 1)
		assert(!video_start_grn);
	always @(posedge i_clk)
	if (fblu_hpos != 1)
		assert(!video_start_blue);
	always @(posedge i_clk)
	if (f_hpos != 2)
		assert(!video_start);

	always @(posedge i_clk)
	if ((f_hpos < 3) || (f_hpos +3 >= fh_width))
		assert(!o_pix_valid);
	else if (f_past_valid && !$past(i_reset) && $past(o_pix_valid))
		assert(o_pix_valid == (f_hpos + 3 < f_hwidth));

	always @(posedge i_clk)
	if (f_hpos + 3 >= fh_width)
	begin
		assert(!o_hsync
			|| (fh_syncpol^o_hsync) == ((f_hpos + 3 >= fh_front)
						&&(f_hpos + 3 < fh_sync)));
	end else if (f_hpos < 3)
		assert(!o_hsync || ((o_hsync^fh_syncpol) == 0));
	// }}}
`endif
// }}}
endmodule
