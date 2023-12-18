////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axinbroadcast.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Broadcasts a packet from a single source to NOUT destinations.
//		Actual chosen destination is selectable.  Does not include
//	any FIFOs--those can follow if necessary.
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
module axinbroadcast #(
		// {{{
		parameter	NOUT = 4,	// Number of incoming eth ports
		parameter	DW = 64,	// Bits per clock cycle
		parameter	WBITS = $clog2(DW/8),
		parameter	LGPOLY = 7,
		parameter [LGPOLY-1:0]	POLYNOMIAL = 7'h41,
		parameter [0:0]	OPT_SKIDBUFFER = 0,
		parameter [0:0]	OPT_LOWPOWER = 0
		// }}}
	) (
		// {{{
		input	wire				i_clk, i_reset,
		input	wire	[NOUT-1:0]		i_cfg_active,
		// Incoming packet interface
		// {{{
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[DW-1:0]	S_DATA,
		input	wire [WBITS-1:0]	S_BYTES,
		input	wire			S_LAST,
		input	wire			S_ABORT,
		//
		// S_PORT tells us which port or port(s) we wish to forward
		// this packet to.  For true broadcasting, S_PORT should be
		// all ones.  For standard routing, S_PORT should be $onehot().
		input	wire [NOUT-1:0]		S_PORT,
		// }}}
		// Outgoing packet, forwarded to NOUT interfaces
		// {{{
		output	reg	[NOUT-1:0]		M_CHREQ,
		input	wire	[NOUT-1:0]		M_ALLOC,
		output	reg	[NOUT-1:0]		M_VALID,
		input	wire	[NOUT-1:0]		M_READY,
		output	reg	[NOUT*DW-1:0]		M_DATA,
		output	reg	[NOUT*WBITS-1:0]	M_BYTES,
		output	reg	[NOUT-1:0]		M_LAST,
		output	reg	[NOUT-1:0]		M_ABORT,
		// }}}
		output	reg	[31:0]			o_debug
		// }}}
	);

	// Local declarations
	// {{{
	genvar	gk;
	wire				skd_valid, skd_ready,
					skd_last, skd_abort;
	wire	[DW-1:0]		skd_data;
	wire	[WBITS-1:0]	skd_bytes;
	wire	[NOUT-1:0]		skd_port;

	reg			s_midpkt;
	reg	[NOUT-1:0]	midpkt;

	reg			open_channel, deadlock;
	reg	[LGPOLY-1:0]	pseudorandom;
	reg	[5:0]		deadlock_counter;
	wire			one_active, full_grant, end_of_packet;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Start with a skidbuffer
	// {{{
	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER

		netskid #(
			.DW(NOUT+DW+WBITS)
		) u_skidbuffer (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.S_AXIN_VALID(S_VALID), .S_AXIN_READY(S_READY),
			.S_AXIN_DATA({ S_PORT, S_BYTES, S_DATA }),
			.S_AXIN_LAST(S_LAST), .S_AXIN_ABORT(S_ABORT),
			//
			.M_AXIN_VALID(skd_valid), .M_AXIN_READY(skd_ready),
			.M_AXIN_DATA({ skd_port, skd_bytes, skd_data }),
			.M_AXIN_LAST(skd_last), .M_AXIN_ABORT(skd_abort)
			// }}}
		);
	end else begin : NO_SKIDBUFFER

		assign	skd_valid = S_VALID;
		assign	S_READY   = skd_ready;
		assign	skd_data  = S_DATA;
		assign	skd_bytes = S_BYTES;
		assign	skd_last  = S_LAST;
		assign	skd_abort = S_ABORT;
		assign	skd_port  = S_PORT;

	end endgenerate

	assign	skd_ready = open_channel
				&& (0 == (M_VALID & ~M_READY & M_CHREQ));
	// }}}

	// s_midpkt
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		s_midpkt <= 0;
	else if (skd_abort && (!skd_valid || skd_ready))
		s_midpkt <= 1'b0;
	else if (skd_valid && skd_ready && !skd_abort)
		s_midpkt <= !skd_last;
	// }}}

	assign	one_active = ONEHOT(skd_port & i_cfg_active);
	assign	end_of_packet = (skd_valid && skd_ready && skd_last)
				|| (skd_abort && (!skd_valid || skd_ready));

	// For a full grant, everything we've requested must be available,
	//	and our request must match the requested skd_port
	assign	full_grant = (0 == ((M_CHREQ ^ M_ALLOC) & i_cfg_active))
			&& (0 == ((M_CHREQ ^ skd_port) & i_cfg_active));

	// open_channel
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		open_channel <= 1'b0;
	else if (end_of_packet)
		open_channel <= 1'b0;
	else if (skd_valid && one_active)
		open_channel <= 1'b1;
	else if (full_grant)
		open_channel <= 1'b1;
	// }}}

	// pseudorandom
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		pseudorandom <= 1;
	else if (skd_valid)
	begin
		if (pseudorandom[0])
			pseudorandom <= (pseudorandom >> 1) ^ POLYNOMIAL;
		else
			pseudorandom <= pseudorandom >> 1;
	end
	// }}}

	// deadlock, deadlock_counter
	// {{{
	always @(posedge i_clk)
	if (i_reset || (M_CHREQ == 0) || (M_CHREQ == M_ALLOC) || open_channel
			|| M_VALID != 0)
		{ deadlock, deadlock_counter } <= 0;
	else if (!deadlock)
		{ deadlock, deadlock_counter } <= deadlock_counter + 1;
	else
		// Verilator lint_off WIDTH
		{ deadlock, deadlock_counter } <= pseudorandom
							+ deadlock_counter;
		// Verilator lint_on  WIDTH
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Generate the outputs
	// {{{
	wire	[NOUT-1:0]	m_end_of_packet;

	assign	m_end_of_packet = (M_VALID & M_READY & M_LAST)
				| (M_ABORT & (~M_VALID | M_READY));

	// M_*
	initial	M_VALID = 0;
	initial	M_DATA  = 0;
	initial	M_BYTES = 0;
	initial	M_LAST  = 0;
	initial	M_ABORT = 0;
	generate for(gk=0; gk<NOUT; gk=gk+1)
	begin : GEN_OUT
		// {{{


		always @(posedge i_clk)
		if (i_reset || !i_cfg_active[gk])
			midpkt[gk] <= 0;
		else if (skd_abort && (!skd_valid || skd_ready))
			midpkt[gk] <= 1'b0;
		else if (skd_valid && skd_ready && skd_port[gk] && !skd_abort)
			midpkt[gk] <= (midpkt[gk] || !s_midpkt) && !skd_last;

		always @(posedge i_clk)
		if (i_reset)
			M_CHREQ[gk] <= 1'b0;
		else if (deadlock && !open_channel)
			M_CHREQ[gk] <= 1'b0;
		else if ((!s_midpkt && skd_valid) && skd_port[gk]
							&& i_cfg_active[gk])
			M_CHREQ[gk] <= 1'b1;
		else if (m_end_of_packet[gk])
			M_CHREQ[gk] <= 1'b0;

		always @(posedge i_clk)
		if (i_reset)
			M_VALID[gk] <= 0;
		else if (!M_VALID[gk] || M_READY[gk])
			M_VALID[gk] <= i_cfg_active[gk]
				&& open_channel
				&& (!s_midpkt || midpkt[gk])
				&& skd_valid && skd_ready
				&& skd_port[gk] && !skd_abort;

		always @(posedge i_clk)
		if (OPT_LOWPOWER && i_reset)
		begin
			M_DATA[ gk*DW +: DW] <= 0;
			M_BYTES[gk*WBITS +: WBITS] <= 0;
			M_LAST[ gk] <= 1'b0;
		end else if (!M_VALID[gk] || M_READY[gk])
		begin
			M_DATA[ gk*DW +: DW] <= skd_data;
			M_BYTES[gk*WBITS +: WBITS] <= skd_bytes;
			M_LAST[ gk] <= skd_last;

			if (OPT_LOWPOWER && (!skd_valid || skd_abort
					|| !skd_ready
					|| !skd_port[gk]
					|| (s_midpkt && !midpkt[gk])
					|| !i_cfg_active[gk]))
			begin
				M_DATA[ gk*DW +: DW] <= 0;
				M_BYTES[gk*WBITS +: WBITS] <= 0;
				M_LAST[ gk] <= 1'b0;
			end
		end

		always @(posedge i_clk)
		if (i_reset)
			M_ABORT[gk] <= 0;
		else if (midpkt[gk] && !i_cfg_active[gk])
			M_ABORT[gk] <= 1'b1;
		else if (midpkt[gk] && skd_abort)
			M_ABORT[gk] <= (!M_VALID[gk] || !M_LAST[gk]);
		else if (!M_VALID[gk] || M_READY[gk])
			M_ABORT[gk] <= 1'b0;
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Debugging outputs
	// {{{
	reg	[7:0]	dbg_watchdog;
	integer	dbgi;

	always @(posedge i_clk)
	if (i_reset || (S_VALID && S_READY))
		dbg_watchdog <= 0;
	else if (s_midpkt&& !dbg_watchdog[7])
		dbg_watchdog <= dbg_watchdog + 1;;


	always @(posedge i_clk)
	begin
		o_debug <= 0;

		for(dbgi=0; dbgi < NOUT; dbgi=dbgi+1)
			o_debug[dbgi*4 +: 4] <= { M_VALID[dbgi], M_READY[dbgi],
				M_VALID[dbgi] && M_LAST[dbgi], M_ABORT[dbgi] };

		o_debug[20 +: NOUT] <= midpkt;
		o_debug[26] <= s_midpkt;
		o_debug[27 +: 4] <= { S_VALID, S_READY, S_LAST, S_ABORT };

		o_debug[31] <= dbg_watchdog[7];
	end
	// }}}

	function	ONEHOT(input [NOUT-1:0] in);
		integer	k;
		reg	tmp;
	begin
		tmp = 0;
		for(k=0; k<NOUT; k=k+1)
			if (in == (1<<k))
				tmp = 1;
		ONEHOT = tmp;
	end endfunction

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
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
	localparam	F_MAX_LENGTH = 1024;
	wire	[10:0]	fslv_word;
	wire	[11:0]	fslv_packets;
	(* anyconst *)	reg	[DW:0]		fnvr_data;
	(* anyconst *)	reg			fc_active;
	(* anyseq *)	reg	[NOUT-1:0]	f_port;
	// reg	[NOUT-1:0]	f_last_active, f_last_port;

	always @(*)
	if (fc_active)
		assume(&i_cfg_active);

	always @(posedge i_clk)
	if (S_VALID || fslv_word != 0 || M_VALID != 0)
		assume($stable(f_port));

	/*
	always @(posedge i_clk)
	if (S_VALID)
	begin
		f_last_active <= i_cfg_active;
		f_last_port   <= S_PORT;
	end
	*/

	always @(*)
	if (S_VALID)
		assume(f_port == S_PORT);

	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{

	faxin_slave #(
		.MAX_LENGTH(F_MAX_LENGTH),
		.DATA_WIDTH(DW), .WBITS(WBITS)
	) fslv (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(S_VALID),
		.S_AXIN_READY(S_READY),
		.S_AXIN_DATA(S_DATA),
		.S_AXIN_BYTES(S_BYTES),
		.S_AXIN_LAST(S_LAST),
		.S_AXIN_ABORT(S_ABORT),
		//
		.f_stream_word(fslv_word),
		.f_packets_rcvd(fslv_packets)
		// }}}
	);

	always @(*)
	if (!i_reset)
	begin
		if (!S_VALID || !S_ABORT)
		begin
			assert(s_midpkt == (fslv_word != 0));
		end else if (fslv_word != 0)
			assert(s_midpkt);
	end

	generate for(gk=0; gk<NOUT; gk=gk+1)
	begin : F_MASTER
		// {{{
		wire	[10:0]	fmst_word;
		wire	[11:0]	fmst_packets;
		(* anyconst *)	reg	fnvr_port;

		faxin_master #(
			.MAX_LENGTH(F_MAX_LENGTH),
			.DATA_WIDTH(DW), .WBITS(WBITS)
		) fmst (
			// {{{
			.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
			//
			.S_AXIN_VALID(M_VALID[gk]),
			.S_AXIN_READY(M_READY[gk]),
			.S_AXIN_DATA(M_DATA[gk*DW +: DW]),
			.S_AXIN_BYTES(M_BYTES[gk*WBITS +: WBITS]),
			.S_AXIN_LAST(M_LAST[gk]),
			.S_AXIN_ABORT(M_ABORT[gk]),
			//
			.f_stream_word(fmst_word),
			.f_packets_rcvd(fmst_packets)
			// }}}
		);

		always @(posedge i_clk)
		if (!i_reset && $past(!i_reset && M_CHREQ[gk] && M_ALLOC[gk]))
			assume(M_ALLOC[gk]);
		always @(posedge i_clk)
		if (open_channel && f_port[gk])
			assume(M_CHREQ[gk] && M_ALLOC[gk]);

		always @(*)
		if (!i_reset)
		begin
			if (!open_channel)
				assert(!M_VALID[gk] || fslv_word == 0);
			if (M_VALID[gk])
			begin
				assert(open_channel || M_LAST[gk] || M_ABORT[gk]);
				assert(f_port[gk]);
				assert(M_CHREQ[gk]);
				if (!M_ABORT[gk])
					assert(M_LAST[gk] == (fslv_word == 0));
				if (fslv_word == 0)
					assert(M_LAST[gk] || M_ABORT[gk]);
				assert(!deadlock);
			end

			if (M_VALID[gk] && !M_ABORT[gk] && !M_LAST)
			begin
				assert(midpkt[gk]);
				if (s_midpkt)
					assert(fslv_word == (fmst_word + (M_VALID[gk] ? 1:0)));
			end

			if (!s_midpkt)
			begin
				assert(!M_VALID[gk] || M_LAST[gk] || M_ABORT[gk]);
			end

			if (!midpkt[gk])
				assert((M_VALID[gk] && M_LAST[gk])|| M_ABORT[gk]
						||(fmst_word == 0));
		end

		always @(*)
		if (!i_reset && (!M_VALID[gk] || !M_LAST[gk]) && !M_ABORT[gk])
			assert(midpkt[gk] == (M_VALID[gk] || fmst_word != 0));

		always @(posedge i_clk)
		if (!i_reset && (!M_VALID[gk] || !M_LAST[gk]) && !M_ABORT[gk])
			assert(!midpkt[gk] || f_port[gk]);

		always @(*)
		if (!i_reset && (M_ABORT[gk] || (M_VALID[gk] && M_LAST[gk])))
			assert(!midpkt[gk] || (S_VALID && S_ABORT));

		always @(*)
		if (!i_reset && (M_VALID[gk] && M_LAST[gk]))
			assert(!midpkt[gk]);

		// always @(posedge i_clk)
		// if (!i_reset && M_VALID[gk] && M_LAST[gk])
		//	assert(!s_midpkt || !fc_port[gk]);

		always @(*)
		if (!i_reset && M_VALID[gk])
			assert({ M_LAST[gk],M_DATA[DW*gk +: DW] } != fnvr_data);

		always @(*)
		if (!i_reset && fnvr_port)
		begin
			assume(!i_cfg_active[gk] || !S_VALID || !S_PORT[gk]);

			// assert(!s_midpkt || !f_port[gk]);
			assert(!midpkt[gk]);
		end

		always @(*)
		if (!i_reset && fnvr_port)
			assert(!M_VALID[gk]);

		always @(*)
		if (!i_reset)
			assert(fmst_word + ((M_VALID[gk] && !M_LAST[gk]) ? 1:0)
				+ 1 <= F_MAX_LENGTH);

		always @(*)
		if (!i_reset && !s_midpkt)
			assert(!midpkt[gk]);

		always @(*)
		if (!i_reset && midpkt[gk] && (!S_VALID || !S_ABORT)
			  &&((!M_VALID[gk] || !M_LAST[gk])&& !M_ABORT[gk]))
			assert(fslv_word == (fmst_word + (M_VALID[gk] ? 1:0)));

		(* anyconst *) reg	fpkt_count_valid;

		always @(*)
		if(fpkt_count_valid)
			assume(i_cfg_active[gk] && (!s_midpkt || f_port[gk]));

		always @(*)
		if(!i_reset && fpkt_count_valid)
		begin
			assume(!fslv_packets[11]);
			assert(fslv_packets == fmst_packets
			  +((M_VALID[gk] && M_LAST[gk] && !M_ABORT[gk]) ? 1:0));

			assert(!s_midpkt || midpkt[gk]);
		end

		// always @(*) if (!i_cfg_active[gk]) assume(!M_VALID[gk]);
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Never properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	(* anyconst *)	reg	fnvr_abort;

	always @(*)
	if (!i_reset && fnvr_abort)
		assume(0 == ((S_VALID || s_midpkt) && S_ABORT));

	always @(*)
	if (!i_reset && fnvr_abort)
		assume((i_cfg_active & midpkt) == midpkt);

	always @(*)
	if (!i_reset && fnvr_abort)
		assert(M_ABORT == 0);

	always @(*)
	if (!i_reset && S_VALID && !S_ABORT)
		assume({ S_LAST, S_DATA } != fnvr_data);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Low power checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate for(gk=0; gk<NOUT; gk=gk+1)
	begin : F_LOWPWR
		always @(*)
		if (!i_reset && OPT_LOWPOWER && !M_VALID[gk])
		begin
			assert(M_DATA[gk*DW +: DW]  == 0);
			assert(M_BYTES[gk*WBITS +: WBITS] == 0);
			assert(M_LAST[gk]  == 0);
		end
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
		cover(!i_reset && M_VALID[0] && M_READY[0] && M_LAST[0] && !M_ABORT[0]);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
`endif
// }}}
endmodule
