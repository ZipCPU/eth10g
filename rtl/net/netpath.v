////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	netpath.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	RTL for the digital path between the packet handling within the
//		design, and the packet handling required to feed and drive the
//	10GBASE-T 66/64B encoders and decoders.  This particular file is little
//	more than glue logic, containing the following paths.
//
//  From RX GTX to FPGA:
//	{{{
//	p66brxgears	-- 64/66b Gearbox: 32bits in, aligned 66bits out.
//				This operates at 312.5MHz.
//	afifo		-- Used to slow us down to 200MHz, now that we are at
//				66b/clock.  (We could slow down by 2x, but we
//				still need some slack, so must be > 156MHz.)
//	p64bscrambler	-- Descrambles the incoming 66-bit words
//	p642pkt		-- Decodes the 66 bit words into 64 bit words, with
//			   active byte counts and a LAST word in packet
//		indicator.  This is where the packets are first converted to
//		the AXIN protocol.  That said, there's still no buffering
//		available.  Any drop in READY will likely cause a packet to be
//		ABORTed here.
//	dropshort	-- ABORTs any packet that doesn't have a full 64 Bytes
//			   to it.
//	crc_axin	-- ABORTs any packet with a failing CRC.
//	axinwidth	-- Converts from a 64b width to a 128b width.  This is
//			   a necessary first step before crossing clock domains
//			   to the system clock (100MHz).
//	axincdc		-- Crosses from the intermediate clock domain (200MHz)
//			   to the system clock domain (100MHz).  The prior
//		jump in width allows us to do this with no more than a
//		guarantee that the system clock has to be faster than half the
//		RX clock.  The AXIN stream resulting from this CDC crossing
//		then goes to the system.
//		
//	rx_activity	-- A quick and dirty counter, used to light an LED
//			   indicating packets have been successfully read.
//	}}}
//  From FPGA to TX GTX:
//	{{{
//	axincdc		-- Cross clock domains from system to intermediate/fast
//			   clock (200MHz).  There's no speed requirement here
//			   since backpressure is fully supported.  That said,
//		the system clock should generall be fast enough to keep a long
//		packet going if it cannot fit in the following buffers.
//	axinwidth	-- Once we move to the tx clock domain, we can downsize
//			   to the width required by the comms port: 64 bits.
//	pktgate		-- Once we get past this point, outgoing packets cannot
//			   be interrupted without getting dropped by the system
//		following.  To ensure we have a bit of a buffer lest things
//		get interrupted, the packet gate waits for either 1) a full
//		packet, or 2) a full buffer before forwarding a packet for
//		transmission.  The purpose here is to be able to ride through
//		any hiccups in the source that might follow--due to clock
//		mismatches or anything else.
//	pkt2p64b	-- Convert from our 64-bit AXI network packet protocol
//			   to the 66-bit word protocol used by the 10GBASE-T
//		protocol.  This includes 66/64b encoding.
//	p64bscrambler	-- As a second half of the encoding step, we scramble
//			   the incoming packet.
//	p66btxgears	-- 66/64b Gearbox: 66bits in, 64bits out to the AFIFO
//	afifo		-- Cross clock domains from the intermediate/fast clock
//			   (200MHz) to the 312.5 MHz required by the PHY.  64b
//			   are moved at a time.
//	(tx_phase)	-- A quick bit of glue logic is used here to convert
//			   from 64b to the 32b PHY interface.  (64b PHY would've
//			   required too many MMCMs, 66b would require too much
//			   nasty synchronization, etc.)
//	}}}
//  Statistic capture:
//	{{{
//		Success statistics are drawn from four locations and moved
//		to the sytem clock domain.  These statistics include the
//		length of a packet upon its conclusion, and whether or not it
//		aborted vs completing naturally.  Also, when packets are
//		complete, a copy of the descrambled 66b RX word is shared.
//		These "stats" are then used to fill a (compressed) wishbone
//		scope with some (hopefully) useful information.
//
//		1. If there's no packets, we should be able to observe IDLE
//			(This will be lucky to ever observe a FAULT)
//		2. If packets are present, we'll observe those packets.
//	}}}
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
module	netpath #(
		// {{{
		parameter	LGPKTGATE=4,
		parameter	LGCDCRAM = 5,
		parameter [0:0]	OPT_SCRAMBLER=1,
		parameter [0:0]	OPT_LITTLE_ENDIAN=0,
		parameter [0:0]	OPT_INVERT_TX = 1'b0,
		localparam	RAWDW =  32,
		localparam	LCLDW =  64,
		localparam	PKTDW = 128
		// }}}
	) (
		// {{{
		input	wire		i_rx_clk, i_tx_clk, i_reset_n,
		input	wire		i_sys_clk, i_fast_clk,
		output	wire		o_link_up, o_activity,
		// PHY interface
		// {{{
		input	wire		i_phy_fault,
		input	wire	[RAWDW-1:0]	i_raw_data,
		output	reg	[RAWDW-1:0]	o_raw_data,
		// }}}
		// Incoming packets to send
		// {{{
		input	wire				S_VALID,
		output	wire				S_READY,
		input	wire	[PKTDW-1:0]		S_DATA,
		input	wire	[$clog2(PKTDW/8)-1:0]	S_BYTES,
		input	wire				S_LAST,
		input	wire				S_ABORT,
		// }}}
		// Outgoing received packets
		// {{{
		output	wire				M_VALID,
		input	wire				M_READY,
		output	wire	[PKTDW-1:0]		M_DATA,
		output	wire	[$clog2(PKTDW/8)-1:0]	M_BYTES,
		output	wire				M_LAST,
		output	wire				M_ABORT,
		// }}}
		output	reg	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	localparam [0:0]	OPT_DROPSHORT = 1'b1;
	localparam [0:0]	OPT_CRC = 1'b1;

	// The clock speed is nominally (10GHz * 66/64) / 64
	//	or about 156.25MHz (or 161.1428..MHz)
	// Packets should keep the LED high for about 1/10th of a second or so
	//	or about 16M clock cyles.  Our counter requires twice that much,
	//	so ...
	//	
	localparam	ACTMSB = 24;
	localparam	LGPKTLN = 16;
	// Verilator lint_off SYNCASYNCNET
	reg		rx_reset_n, tx_reset_n, fast_reset_n;
	// Verilator lint_on  SYNCASYNCNET
	reg	[1:0]	rx_reset_pipe, tx_reset_pipe, fast_reset_pipe;

	wire		rx66b_valid;
	wire	[65:0]	rx66b_data;

	wire		tx66b_ready, ign_tx66b_valid;
	wire	[65:0]	tx66b_data;

	wire		rx_valid, rx_ready;
	wire	[65:0]	rx_data;
	wire		remote_fault, local_fault;
	wire		rx_link_up, tx_link_up;

	wire		SRC_VALID, SRC_READY, SRC_LAST, SRC_ABORT;
	wire	[LCLDW-1:0]	SRC_DATA;
	wire	[$clog2(LCLDW/8)-1:0]	SRC_BYTES;

	wire		PKT_VALID, PKT_READY, PKT_LAST, PKT_ABORT;
	wire	[LCLDW-1:0]	PKT_DATA;
	wire	[$clog2(LCLDW/8)-1:0]	PKT_BYTES;

	wire		tx_ready, ign_tx_high, ign_rx_high;
	wire	[65:0]	tx_data;

	reg	[ACTMSB:0]	tx_activity, rx_activity;
	reg	tx_phase;

	wire		TXCK_VALID, TXCK_READY, TXCK_LAST, TXCK_ABORT;
	wire	[PKTDW-1:0]	TXCK_DATA;
	wire	[$clog2(PKTDW/8)-1:0]	TXCK_BYTES;

	wire		TXWD_VALID, TXWD_READY, TXWD_LAST, TXWD_ABORT;
	wire	[LCLDW-1:0]	TXWD_DATA;
	wire	[$clog2(LCLDW/8)-1:0]	TXWD_BYTES;

	wire		FULL_VALID, FULL_READY, FULL_LAST, FULL_ABORT;
	wire	[LCLDW-1:0]	FULL_DATA;
	wire	[$clog2(LCLDW/8)-1:0]	FULL_BYTES;

	wire		CRC_VALID, CRC_READY, CRC_LAST, CRC_ABORT;
	wire	[LCLDW-1:0]	CRC_DATA;
	wire	[$clog2(LCLDW/8)-1:0]	CRC_BYTES;

	wire		RXWD_VALID, RXWD_READY, RXWD_LAST, RXWD_ABORT;
	wire	[PKTDW-1:0]	RXWD_DATA;
	wire	[$clog2(PKTDW/8)-1:0]	RXWD_BYTES;

	// wire		RXCK_VALID, RXCK_READY, RXCK_LAST, RXCK_ABORT;
	// wire	[PKTDW-1:0]	RXCK_DATA;
	// wire	[$clog2(PKTDW/8)-1:0]	RXCK_BYTES;
	wire	[PKTDW-1:0]	unswapped_m_data;

	wire		rx_fast_ready, rx_fast_valid, rx_fast_empty,
			ign_rx66b_full;
	wire	[65:0]	rx_fast_data;

	wire		ign_tx_fast_empty, tx64b_full;
	wire	[63:0]	tx_fast_data;
	wire	[63:0]	tx64b_data;

	wire	stat_gate_valid, stat_tx_valid, stat_crc_valid, stat_src_valid;
	wire	[LGPKTLN+1:0]	stat_gate_data, stat_tx_data,
				stat_crc_data, stat_src_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronize resets
	// {{{
	always @(posedge i_fast_clk or negedge i_reset_n)
	if (!i_reset_n)
		{ fast_reset_n, fast_reset_pipe } <= 0;
	else
		{ fast_reset_n, fast_reset_pipe } <= { fast_reset_pipe, i_reset_n };

	always @(posedge i_rx_clk or negedge i_reset_n)
	if (!i_reset_n)
		{ rx_reset_n, rx_reset_pipe } <= 0;
	else
		{ rx_reset_n, rx_reset_pipe } <= { rx_reset_pipe, i_reset_n };

	always @(posedge i_tx_clk or negedge i_reset_n)
	if (!i_reset_n)
		{ tx_reset_n, tx_reset_pipe } <= 0;
	else
		{ tx_reset_n, tx_reset_pipe } <= { tx_reset_pipe, i_reset_n };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming packet -> M_* processing
	// {{{

	// 32:66b Gearbox
	// {{{
	p66brxgears
	u_p66brxgears (
		.i_clk(i_rx_clk), .i_reset(!rx_reset_n),
		.i_data(i_raw_data),
		.M_VALID(rx66b_valid),
		.M_DATA( rx66b_data)
	);
	// }}}

	// Cross clock domains: RX_CLK to 200MHz
	// {{{
	afifo #(
		.LGFIFO(LGCDCRAM),
		.WIDTH(66)
	) rx_afifo (
		.i_wclk(i_rx_clk), .i_wr_reset_n(rx_reset_n),
		.i_wr(rx66b_valid),
		.i_wr_data(rx66b_data),
		.o_wr_full(ign_rx66b_full),

		.i_rclk(i_fast_clk), .i_rd_reset_n(fast_reset_n),
		.i_rd(rx_fast_ready),
		.o_rd_data(rx_fast_data),
		.o_rd_empty(rx_fast_empty)
	);
	assign	rx_fast_valid = !rx_fast_empty;
	// }}}

	// Descramble the incoming data
	// {{{
	p64bscrambler #(
		.OPT_RX(1'b1), .OPT_ENABLE(OPT_SCRAMBLER)
	) u_descrambler (
		// {{{
		.i_clk(i_fast_clk), .i_reset_n(fast_reset_n),
		.i_valid(rx_fast_valid),
		.o_ready(rx_fast_ready),
		.i_data(rx_fast_data),
		//
		.o_valid(rx_valid),
		.i_ready(rx_ready),
		.o_data(rx_data)
		// }}}
	);
	// }}}

	// Convert from 66b (near XGMII) to AXI network packet format
	// {{{
	p642pkt
	u_p642pkt (
		// {{{
		.RX_CLK(i_fast_clk), .S_ARESETN(fast_reset_n),
		//
		.i_phy_fault(i_phy_fault),
		.o_remote_fault(remote_fault),
		.o_local_fault(local_fault),
		.o_link_up(rx_link_up),
		//
		.RX_VALID(rx_valid),
		.RX_DATA(rx_data),
		//
		.M_VALID(SRC_VALID),
		.M_READY(SRC_READY),
		.M_DATA(SRC_DATA),
		.M_BYTES(SRC_BYTES),
		.M_ABORT(SRC_ABORT),
		.M_LAST(SRC_LAST)
		// }}}
	);

	assign	rx_ready = 1'b1;

	// Count packets, generate stats
	// {{{
	pktcount #(
		.LGPKTLN(LGPKTLN)
	) u_src_stats (
		// {{{
		.i_clk(i_fast_clk), .i_reset(!fast_reset_n),
		//
		.S_VALID(SRC_VALID && SRC_READY),
		.S_BYTES(SRC_BYTES), .S_LAST(SRC_LAST), .S_ABORT(SRC_ABORT),
		//
		.M_VALID(stat_src_valid),
		.M_READY(1'b1),
		.M_DATA(stat_src_data)
		// }}}
	);
	// }}}
	// }}}

	// Drop short packets--anything less than 64 bytes
	// {{{
	generate if (OPT_DROPSHORT)
	begin : GEN_DROPSHORT
		dropshort #(
			.DW(64)
		) u_dropshort (
			// {{{
			.S_CLK(i_fast_clk), .S_ARESETN(fast_reset_n),
			//
			.S_VALID(SRC_VALID),
			.S_READY(SRC_READY),
			.S_DATA( SRC_DATA),
			.S_BYTES(SRC_BYTES),
			.S_ABORT(SRC_ABORT),
			.S_LAST( SRC_LAST),
			//
			.M_VALID(PKT_VALID),
			.M_READY(PKT_READY),
			.M_DATA( PKT_DATA),
			.M_BYTES(PKT_BYTES),
			.M_ABORT(PKT_ABORT),
			.M_LAST( PKT_LAST)
			// }}}
		);
	end else begin : NO_DROPSHORT
		assign	PKT_VALID = SRC_VALID;
		assign	SRC_READY = PKT_READY;
		assign	PKT_DATA  = SRC_DATA;
		assign	PKT_BYTES = SRC_BYTES;
		assign	PKT_ABORT = SRC_ABORT;
		assign	PKT_LAST  = SRC_LAST;
	end endgenerate
	// }}}

	// Check CRCs, drop packets that don't match
	// {{{
	generate if (OPT_CRC)
	begin : GEN_CRC_CHECK
		// Verilator lint_off UNUSED
		wire	ign_high;
		// Verilator lint_on  UNUSED

		crc_axin #(
			.DATA_WIDTH(64), .OPT_SKIDBUFFER(1'b1),
			.OPT_LOWPOWER(1'b0)
		) u_check_crc (
			// {{{
			.ACLK(i_fast_clk), .ARESETN(fast_reset_n),
			.i_cfg_en(1'b1),
			//
			.S_AXIN_VALID(PKT_VALID),
			.S_AXIN_READY(PKT_READY),
			.S_AXIN_DATA( PKT_DATA),
			.S_AXIN_BYTES({ (PKT_BYTES==0), PKT_BYTES }),
			.S_AXIN_LAST( PKT_LAST),
			.S_AXIN_ABORT(PKT_ABORT),
			//
			.M_AXIN_VALID(CRC_VALID),
			.M_AXIN_READY(CRC_READY),
			.M_AXIN_DATA( CRC_DATA),
			.M_AXIN_BYTES({ ign_high, CRC_BYTES }),
			.M_AXIN_LAST( CRC_LAST),
			.M_AXIN_ABORT(CRC_ABORT)
			// }}}
		);

	end else begin : NO_CRC_CHECK
		assign	CRC_VALID = PKT_VALID;
		assign	PKT_READY = CRC_READY;
		assign	CRC_DATA  = PKT_DATA;
		assign	CRC_BYTES = PKT_BYTES;
		assign	CRC_LAST  = PKT_LAST;
		assign	CRC_ABORT = PKT_ABORT;
	end endgenerate

	pktcount #(
		.LGPKTLN(LGPKTLN)
	) u_crc_stats (
		// {{{
		.i_clk(i_fast_clk), .i_reset(!fast_reset_n),
		//
		.S_VALID(CRC_VALID && CRC_READY),
		.S_BYTES(CRC_BYTES), .S_LAST(CRC_LAST), .S_ABORT(CRC_ABORT),
		//
		.M_VALID(stat_crc_valid),
		.M_READY(1'b1),
		.M_DATA(stat_crc_data)
		// }}}
	);
	// }}}

	// Width conversion--from 64b to PKTDW (128b) bits
	// {{{
	axinwidth #(
		.IW(64), .OW(PKTDW)
	) u_rxwidth (
		// {{{
		.ACLK(i_fast_clk), .ARESETN(fast_reset_n),
		//
		.S_AXIN_VALID(CRC_VALID),
		.S_AXIN_READY(CRC_READY),
		.S_AXIN_DATA( CRC_DATA),
		.S_AXIN_BYTES({ (CRC_BYTES==0), CRC_BYTES }),
		.S_AXIN_LAST( CRC_LAST),
		.S_AXIN_ABORT(CRC_ABORT),
		//
		.M_AXIN_VALID(RXWD_VALID),
		.M_AXIN_READY(RXWD_READY),
		.M_AXIN_DATA( RXWD_DATA),
		.M_AXIN_BYTES({ ign_rx_high, RXWD_BYTES }),
		.M_AXIN_LAST( RXWD_LAST),
		.M_AXIN_ABORT(RXWD_ABORT)
		// }}}
	);
	// }}}

	// CDC -- switch to the bus clock
	// {{{
	axincdc #(
		.DW(PKTDW),
		.LGFIFO(LGCDCRAM)
	) u_rxcdc (
		// {{{
		.S_CLK(i_fast_clk), .S_ARESETN(fast_reset_n),
		//
		.S_VALID(RXWD_VALID),
		.S_READY(RXWD_READY),
		.S_DATA( RXWD_DATA),
		.S_BYTES(RXWD_BYTES),
		.S_LAST( RXWD_LAST),
		.S_ABORT(RXWD_ABORT),
		//
		.M_CLK(i_sys_clk), .M_ARESETN(i_reset_n),
		//
		.M_VALID(M_VALID),
		.M_READY(M_READY),
		.M_DATA( unswapped_m_data),
		.M_BYTES(M_BYTES),
		.M_LAST( M_LAST),
		.M_ABORT(M_ABORT)
		// }}}
	);
	// }}}

	assign	M_DATA =(!OPT_LITTLE_ENDIAN) ? SWAP_ENDIAN_PKT(unswapped_m_data)
				: unswapped_m_data;

	// rx_activity
	// {{{
	always @(posedge i_sys_clk or negedge i_reset_n)
	if (!i_reset_n)
		rx_activity <= 0;
	else if (M_VALID && M_LAST && !M_ABORT)
		rx_activity <= -1;
	else if (rx_activity != 0)
		rx_activity <= rx_activity - 1;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing S_* -> packet processing
	// {{{

	axincdc #(
		.DW(PKTDW),
		.LGFIFO(LGCDCRAM)
	) u_txcdc (
		// {{{
		.S_CLK(i_sys_clk), .S_ARESETN(i_reset_n),
		//
		.S_VALID(S_VALID),
		.S_READY(S_READY),
		.S_DATA((OPT_LITTLE_ENDIAN) ? S_DATA : SWAP_ENDIAN_PKT(S_DATA)),
		.S_BYTES(S_BYTES),
		.S_LAST( S_LAST),
		.S_ABORT(S_ABORT),
		//
		.M_CLK(i_fast_clk), .M_ARESETN(fast_reset_n),
		//
		.M_VALID(TXCK_VALID),
		.M_READY(TXCK_READY),
		.M_DATA( TXCK_DATA),
		.M_BYTES(TXCK_BYTES),
		.M_LAST( TXCK_LAST),
		.M_ABORT(TXCK_ABORT)
		// }}}
	);

	axinwidth #(
		.IW(PKTDW), .OW(64)
	) u_txwidth (
		// {{{
		.ACLK(i_fast_clk), .ARESETN(fast_reset_n),
		//
		.S_AXIN_VALID(TXCK_VALID),
		.S_AXIN_READY(TXCK_READY),
		.S_AXIN_DATA( TXCK_DATA),
		.S_AXIN_BYTES({ (TXCK_BYTES==0), TXCK_BYTES }),
		.S_AXIN_LAST( TXCK_LAST),
		.S_AXIN_ABORT(TXCK_ABORT),
		//
		.M_AXIN_VALID(TXWD_VALID),
		.M_AXIN_READY(TXWD_READY),
		.M_AXIN_DATA( TXWD_DATA),
		.M_AXIN_BYTES({ ign_tx_high, TXWD_BYTES }),
		.M_AXIN_LAST( TXWD_LAST),
		.M_AXIN_ABORT(TXWD_ABORT)
		// }}}
	);

	pktcount #(
		.LGPKTLN(LGPKTLN)
	) u_in_stats (
		// {{{
		.i_clk(i_fast_clk), .i_reset(!fast_reset_n),
		//
		.S_VALID(TXWD_VALID && TXWD_READY),
		.S_BYTES(TXWD_BYTES), .S_LAST(TXWD_LAST), .S_ABORT(TXWD_ABORT),
		//
		.M_VALID(stat_tx_valid),
		.M_READY(1'b1),
		.M_DATA(stat_tx_data)
		// }}}
	);

	// Hold packets until we have a full and complete one
	// {{{
	pktgate #(
		.DW(64), .LGFLEN(LGPKTGATE)
	) u_pktgate (
		// {{{
		.S_AXI_ACLK(i_fast_clk), .S_AXI_ARESETN(fast_reset_n),
		//
		.S_AXIN_VALID(TXWD_VALID),
		.S_AXIN_READY(TXWD_READY),
		.S_AXIN_DATA( TXWD_DATA),
		.S_AXIN_BYTES(TXWD_BYTES),
		.S_AXIN_LAST( TXWD_LAST),
		.S_AXIN_ABORT(TXWD_ABORT),
		//
		.M_AXIN_VALID(FULL_VALID),
		.M_AXIN_READY(FULL_READY),
		.M_AXIN_DATA( FULL_DATA),
		.M_AXIN_BYTES(FULL_BYTES),
		.M_AXIN_LAST( FULL_LAST),
		.M_AXIN_ABORT(FULL_ABORT)
		// }}}
	);

	pktcount #(
		.LGPKTLN(LGPKTLN)
	) u_tx_stats (
		// {{{
		.i_clk(i_fast_clk), .i_reset(!fast_reset_n),
		//
		.S_VALID(FULL_VALID && FULL_READY),
		.S_BYTES(FULL_BYTES), .S_LAST(FULL_LAST), .S_ABORT(FULL_ABORT),
		//
		.M_VALID(stat_gate_valid),
		.M_READY(1'b1),
		.M_DATA(stat_gate_data)
		// }}}
	);
	// }}}

	// Convert from AXI Net Packets to the p66b (near XGMII) format
	// {{{
	pkt2p64b
	u_pkt2p64b (
		// {{{
		.TX_CLK(i_fast_clk), .S_ARESETN(fast_reset_n),
		//
		.i_remote_fault(remote_fault),
				.i_local_fault(local_fault || !rx_reset_n),
		//
		.S_VALID(FULL_VALID),
		.S_READY(FULL_READY),
		.S_DATA( FULL_DATA),
		.S_BYTES(FULL_BYTES),
		.S_LAST( FULL_LAST),
		.S_ABORT(FULL_ABORT),
		//
		.TXREADY(tx_ready),
		.TXDATA(tx_data)
		// }}}
	);
	// }}}

	// Scramble the (near XGMII) data
	// {{{
	p64bscrambler #(
		.OPT_RX(1'b0), .OPT_ENABLE(OPT_SCRAMBLER)
	) u_scrambler (
		// {{{
		.i_clk(i_fast_clk), .i_reset_n(fast_reset_n),
		//
		.i_valid(1'b1),
		.o_ready(tx_ready),
		.i_data( tx_data ^ {(66){OPT_INVERT_TX}}),
		//
		.o_valid(ign_tx66b_valid),
		.i_ready(tx66b_ready),
		.o_data( tx66b_data)
		// }}}
	);
	// }}}

	// 66:64b Gearbox
	// {{{
	p66btxgears
	u_p66btxgears (
		.i_clk(i_fast_clk), .i_reset(!fast_reset_n),
		.S_READY(tx66b_ready),
		.S_DATA( tx66b_data),
		.i_ready(!tx64b_full),
		.o_data(tx64b_data)
	);
	// }}}

	// CDC: Move TX packets to TX clock domain
	// {{{
	afifo #(
		.LGFIFO(LGCDCRAM),
		.WIDTH(64)
	) tx_afifo (
		.i_wclk(i_fast_clk), .i_wr_reset_n(fast_reset_n),
		.i_wr(1'b1),
		.i_wr_data(tx64b_data),
		.o_wr_full(tx64b_full),

		.i_rclk(i_tx_clk), .i_rd_reset_n(tx_reset_n),
		.i_rd(tx_phase),
		.o_rd_data(tx_fast_data),
		.o_rd_empty(ign_tx_fast_empty)
	);
	// }}}

	// 64:32b gearbox
	// {{{
	always @(posedge i_tx_clk or negedge tx_reset_n)
	if (!tx_reset_n)
		tx_phase <= 0;
	else
		tx_phase <= !tx_phase;

	always @(posedge i_tx_clk)
		o_raw_data<=(tx_phase)? tx_fast_data[63:32]:tx_fast_data[31:0];
	// }}}

	assign	tx_link_up = tx_reset_n;

	// tx_activity checking
	// {{{
	always @(posedge i_sys_clk or negedge i_reset_n)
	if (!i_reset_n)
		tx_activity <= 0;
	else if (S_VALID)
		tx_activity <= -1;
	else if (tx_activity != 0)
		tx_activity <= tx_activity - 1;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Debug output
	// {{{
	wire		fast_dbg_valid, fast_dbgfifo_full, dbgfifo_empty;
	wire	[30:0]	fast_dbg_data;
	wire	[30:0]	dbgfifo_data;

	netdbggen
	u_gendebug (
		.i_clk(i_fast_clk), .i_reset(!fast_reset_n),
		.i_phy_fault(i_phy_fault),
		.i_remote_fault(remote_fault), .i_local_fault(local_fault),
		//
		.i_p66b_valid(rx_valid && rx_ready), .i_p66b_data(rx_data),
		// .i_p66b_valid(tx_ready), .i_p66b_data(tx_data),
		//
		.i_rx_packet(stat_src_valid), .i_rx_pktlen(stat_src_data),
		.i_crc_packet(stat_crc_valid), .i_crc_pktlen(stat_crc_data),
		.i_tx_packet(stat_tx_valid),
			.i_tx_pktlen(stat_tx_data),
		.i_txgate_packet(stat_gate_valid),
			.i_txgate_pktlen(stat_gate_data),
		//
		.o_dbg_valid(fast_dbg_valid),
		.i_dbg_ready(!fast_dbgfifo_full),
		.o_dbg_data(fast_dbg_data)
	);

	afifo #(
		.LGFIFO(5), .WIDTH(31), .OPT_REGISTER_READS(1'b0)
	) u_stat_afifo (
		.i_wclk(i_fast_clk), .i_wr_reset_n(fast_reset_n),
		.i_wr(fast_dbg_valid), .i_wr_data(fast_dbg_data),
			.o_wr_full(fast_dbgfifo_full),
		//
		.i_rclk(i_sys_clk), .i_rd_reset_n(i_reset_n),
		.i_rd(1'b1), .o_rd_data(dbgfifo_data),
			.o_rd_empty(dbgfifo_empty)
	);

	always @(posedge i_sys_clk)
	if (!dbgfifo_empty)
		o_debug <= { 1'b1, dbgfifo_data };
	// }}}

	assign	o_link_up = rx_link_up && tx_link_up;
	assign	o_activity = rx_activity[ACTMSB] || tx_activity[ACTMSB];

	function automatic [PKTDW-1:0] SWAP_ENDIAN_PKT(input [PKTDW-1:0] in);
		// {{{
		integer	ib;
		reg	[PKTDW-1:0]	r;
	begin
		r = 0;
		for(ib=0; ib<PKTDW; ib=ib+8)
			r[ib +: 8] = in[PKTDW-8-ib +: 8];
		SWAP_ENDIAN_PKT = r;
	end endfunction
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_on  UNUSED
	// Verilator coverage_off
	wire	unused;
	assign	unused =  &{ 1'b0,
				ign_tx_high, ign_rx_high,
				ign_tx66b_valid,
				ign_rx66b_full, ign_tx_fast_empty };
	// Verilator coverage_on
	// Verialtor lint_off UNUSED
	// }}}
endmodule
