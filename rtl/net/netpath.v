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
//	p66brxgears	-- 64/66b Gearbox: 64bits in, aligned 66bits out
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
//			   a necessary first step before crossing clock domains.
//	axincdc		-- Crosses from the clock domain of the GTX receive
//			   transceiver to the system clock domain.  The prior
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
//	axincdc		-- Cross clock domains from system to tx clock.  There's
//			   no speed requirement here, although the system clock
//		should generall be fast enough to keep a long packet going if
//		it cannot fit in the following buffers.
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
//	p66btxgears	-- 66/64b Gearbox: 66bits in, 64bits out to the PHY
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
		output	wire	[RAWDW-1:0]	o_raw_data,
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
		output	wire				M_ABORT
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	// The clock speed is nominally (10GHz * 66/64) / 64
	//	or about 156.25MHz (or 161.1428..MHz)
	// Packets should keep the LED high for about 1/10th of a second or so
	//	or about 16M clock cyles.  Our counter requires twice that much,
	//	so ...
	//	
	localparam	ACTMSB = 24;
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

	wire		PKT_VALID, PKT_READY, PKT_LAST, PKT_ABORT, ign_high;
	wire	[LCLDW-1:0]	PKT_DATA;
	wire	[$clog2(LCLDW/8)-1:0]	PKT_BYTES;

	wire		tx_ready, ign_tx_high, ign_rx_high;
	wire	[65:0]	tx_data;

	reg	[ACTMSB:0]	tx_activity, rx_activity;

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

	wire		tx_fast_ready, tx66b_full, ign_tx_fast_empty;
	wire	[65:0]	tx_fast_data;

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

	p66brxgears
	u_p66brxgears (
		.i_clk(i_rx_clk), .i_reset(!rx_reset_n),
		.i_data(i_raw_data),
		.M_VALID(rx66b_valid),
		.M_DATA( rx66b_data)
	);

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

	p64bscrambler #(
		.OPT_RX(1'b1), .OPT_ENABLE(OPT_SCRAMBLER)
	) u_descrambler (
		// {{{
		.i_clk(i_fast_clk), .i_reset_n(rx_reset_n),
		.i_valid(rx_fast_valid),
		.o_ready(rx_fast_ready),
		.i_data(rx_fast_data),
		//
		.o_valid(rx_valid),
		.i_ready(rx_ready),
		.o_data(rx_data)
		// }}}
	);

	p642pkt
	u_p642pkt (
		// {{{
		.RX_CLK(i_fast_clk), .S_ARESETN(rx_reset_n),
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

	dropshort #(
		.DW(64)
	) u_dropshort (
		// {{{
		.S_CLK(i_fast_clk), .S_ARESETN(rx_reset_n),
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

	crc_axin #(
		.DATA_WIDTH(64), .OPT_SKIDBUFFER(1'b1), .OPT_LOWPOWER(1'b0)
	) u_check_crc (
		// {{{
		.ACLK(i_fast_clk), .ARESETN(rx_reset_n),
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

	axinwidth #(
		.IW(64), .OW(PKTDW)
	) u_rxwidth (
		// {{{
		.ACLK(i_fast_clk), .ARESETN(rx_reset_n),
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

	axincdc #(
		.DW(PKTDW),
		.LGFIFO(LGCDCRAM)
	) u_rxcdc (
		// {{{
		.S_CLK(i_fast_clk), .S_ARESETN(rx_reset_n),
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

	assign	M_DATA =(!OPT_LITTLE_ENDIAN) ? SWAP_ENDIAN_PKT(unswapped_m_data)
				: unswapped_m_data;

	always @(posedge i_fast_clk or negedge rx_reset_n)
	if (!rx_reset_n)
		rx_activity <= 0;
	else if (M_VALID && M_LAST && !M_ABORT)
		rx_activity <= -1;
	else if (rx_activity != 0)
		rx_activity <= rx_activity - 1;

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
		.M_CLK(i_fast_clk), .M_ARESETN(tx_reset_n),
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
		.ACLK(i_sys_clk), .ARESETN(tx_reset_n),
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

	pktgate #(
		.DW(64), .LGFLEN(LGPKTGATE)
	) u_pktgate (
		// {{{
		.S_AXI_ACLK(i_fast_clk), .S_AXI_ARESETN(tx_reset_n),
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

	pkt2p64b
	u_pkt2p64b (
		// {{{
		.TX_CLK(i_fast_clk), .S_ARESETN(tx_reset_n),
		//
		.i_remote_fault(remote_fault),
				.i_local_fault(local_fault || rx_reset_n),
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

	p64bscrambler #(
		.OPT_RX(1'b0), .OPT_ENABLE(OPT_SCRAMBLER)
	) u_scrambler (
		// {{{
		.i_clk(i_fast_clk), .i_reset_n(tx_reset_n),
		//
		.i_valid(1'b1),
		.o_ready(tx_ready),
		.i_data( tx_data),
		//
		.o_valid(ign_tx66b_valid),
		.i_ready(tx66b_ready),
		.o_data( tx66b_data)
		// }}}
	);

	afifo #(
		.LGFIFO(LGCDCRAM),
		.WIDTH(66)
	) tx_afifo (
		.i_wclk(i_fast_clk), .i_wr_reset_n(fast_reset_n),
		.i_wr(1'b1),
		.i_wr_data(tx66b_data),
		.o_wr_full(tx66b_full),

		.i_rclk(i_tx_clk), .i_rd_reset_n(tx_reset_n),
		.i_rd(tx_fast_ready),
		.o_rd_data(tx_fast_data),
		.o_rd_empty(ign_tx_fast_empty)
	);
	assign	tx66b_ready = !tx66b_full;

	p66btxgears
	u_p66btxgears (
		.i_clk(i_tx_clk), .i_reset(!tx_reset_n),
		.S_READY(tx_fast_ready),
		.S_DATA( tx_fast_data),
		.o_data(o_raw_data)
	);

	assign	tx_link_up = tx_reset_n;

	always @(posedge i_sys_clk or negedge i_reset_n)
	if (!i_reset_n)
		tx_activity <= 0;
	else if (S_VALID)
		tx_activity <= -1;
	else if (tx_activity != 0)
		tx_activity <= tx_activity - 1;

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
	assign	unused =  &{ 1'b0, ign_high,
				ign_tx_high, ign_rx_high,
				ign_tx66b_valid,
				ign_rx66b_full, ign_tx_fast_empty };
	// Verilator coverage_on
	// Verialtor lint_off UNUSED
	// }}}
endmodule
