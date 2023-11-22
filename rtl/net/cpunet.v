////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	cpunet.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Encapsulates the CPU network processing RTL.  This primarily
//		consists of both read and write virtual packet FIFOs, but also
//	a MAC checker (to thin the incoming stream), and (potentially) some
//	width converters.
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
`timescale	1ns / 1ps
`default_nettype none
// }}}
module	cpunet #(
		// {{{
		parameter	BUSDW = 512, AW = 30-$clog2(BUSDW/8),
		parameter	PKTDW = 128,
		parameter [47:0]	CPU_MAC = 48'h1434_afa8_1234,
		parameter [31:0] CPU_IP  ={ 8'd192, 8'd168, 8'd15, 8'd1 },
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter	LGPIPE = 6,
		parameter	LGIFIFO = 5, LGOFIFO = 5
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Control interface, for both virtual packet FIFOs
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[4:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		// }}}
		// Incoming/received packets
		// {{{
		input	wire				RX_VALID,
		output	wire				RX_READY,
		input	wire	[PKTDW-1:0]		RX_DATA,
		input	wire	[$clog2(PKTDW/8)-1:0]	RX_BYTES,
		input	wire				RX_LAST,
		input	wire				RX_ABORT,
		// }}}
		// Outgoing/transmit packets
		// {{{
		output	wire				TX_VALID,
		input	wire				TX_READY,
		output	wire	[PKTDW-1:0]		TX_DATA,
		output	wire	[$clog2(PKTDW/8)-1:0]	TX_BYTES,
		output	wire				TX_LAST,
		output	reg				TX_ABORT,
		// }}}
		// DMA bus interface
		// {{{
		output	wire			o_dma_cyc, o_dma_stb, o_dma_we,
		output	wire [AW-1:0]		o_dma_addr,
		output	wire [BUSDW-1:0]	o_dma_data,
		output	wire [BUSDW/8-1:0]	o_dma_sel,
		input	wire			i_dma_stall,
		input	wire			i_dma_ack,
		input	wire [BUSDW-1:0]	i_dma_data,
		input	wire			i_dma_err,
		// }}}
		output	reg			o_rx_int, o_tx_int,
		output	wire	[31:0]		o_debug
		// }}}
	);

	// Local declarations
	// {{{
	localparam	BUSLSB = $clog2(BUSDW/8);
	// Address definitions
	// {{{
	localparam	[4:0]	ADDR_CONTROL = 5'h00, // promiscuous, memerr,
				// Verilator lint_off UNUSED
				ADDR_MYMAC1  = 5'h01,
				ADDR_MYMAC2  = 5'h02,
				ADDR_MYIP    = 5'h03,
				ADDR_MYIPV61 = 5'h04,
				ADDR_MYIPV62 = 5'h05,
				ADDR_MYIPV63 = 5'h06,
				ADDR_MYIPV64 = 5'h07,
				//
				// Packet counters.  With each packet counter,
				// a write to the register should clear the
				// counter.
				ADDR_RXDROPS= 5'h08,	// RX RCVD, but dropped
				ADDR_RXPKTS = 5'h09,	// RCVD packet count
				ADDR_TXPKTS = 5'h0a,	// Transmitted pkt count
				//
				// Virtual packet FIFO configs
				ADDR_RDBASE = 5'h10,	// TX BASE
				ADDR_RDSIZE = 5'h11,	// TX MEMLEN
				ADDR_RDWPTR = 5'h12,
				ADDR_RDRPTR = 5'h13,
				ADDR_WRBASE = 5'h14,	// RX BASE
				ADDR_WRSIZE = 5'h15,	// RX MEMLEN
				ADDR_WRWPTR = 5'h16,
				ADDR_WRRPTR = 5'h17;
				// Verilator lint_on UNUSED
	// }}}
	// wire	MY_VALID, MY_READY, MY_LAST, MY_ABORT;
	// wire	[PKTDW-1:0]		MY_DATA;
	// wire	[$clog2(PKTDW/8)-1:0]	MY_BYTES;

	wire			wr_wb_cyc, wr_wb_stb, wr_wb_we;
	wire	[AW-1:0]	wr_wb_addr;
	wire	[BUSDW-1:0]	wr_wb_data;
	wire	[(BUSDW/8)-1:0]	wr_wb_sel;
	wire			wr_wb_stall, wr_wb_ack;
	wire	[BUSDW-1:0]	wr_wb_idata;
	wire			wr_wb_err;

	wire			rd_wb_cyc, rd_wb_stb, rd_wb_we;
	wire	[AW-1:0]	rd_wb_addr;
	wire	[BUSDW-1:0]	rd_wb_data;
	wire	[(BUSDW/8)-1:0]	rd_wb_sel;
	wire			rd_wb_stall, rd_wb_ack;
	wire	[BUSDW-1:0]	rd_wb_idata;
	wire			rd_wb_err;

	wire				my_valid, my_ready,my_last, my_abort;
	wire	[PKTDW-1:0]		my_data;
	wire	[$clog2(PKTDW/8)-1:0]	my_bytes;

	wire	ipkt_valid, ipkt_ready, ipkt_last, ipkt_abort;
	wire	[BUSDW-1:0]		ipkt_data;
	wire	[$clog2(BUSDW/8)-1:0]	ipkt_bytes;
	wire				ign_ipkt_msb;

	wire	wide_valid, wide_ready, wide_last, wide_abort;
	wire	[BUSDW-1:0]		wide_data;
	wire	[$clog2(BUSDW/8)-1:0]	wide_bytes;

	wire				mem_valid, mem_last;
	wire	[BUSDW-1:0]		mem_data;
	wire	[$clog2(BUSDW/8)-1:0]	mem_bytes;

	wire	memfifo_valid, memfifo_ready, memfifo_rd, memfifo_last,
					memfifo_empty;
	wire	[BUSDW-1:0]		memfifo_data;
	wire	[$clog2(BUSDW/8)-1:0]	memfifo_bytes;

	reg	[31:0]	pkt_rxdrops, pkt_rxcount, pkt_txcount;
	reg	r_en, r_promiscuous, mem_err, reset_rdfifo, reset_wrfifo,
				mid_rxpkt;
	reg	[AW-1:0]	wr_baseaddr, wr_memsize,
				rd_baseaddr, rd_memsize;
	reg	[BUSLSB+AW-3:0]	wr_readptr,  rd_writeptr;
	wire	[BUSLSB+AW-3:0]	wr_writeptr, rd_readptr;

	wire			clear_counters, rd_fifo_err;
	wire			ign_mem_full;
	wire	[LGOFIFO:0]	ign_mem_fill;

	wire	ign_mbytes_lsb, ign_outw_abort;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Control logic
	// {{{

	always @(posedge i_clk)
	if (i_reset)
	begin
		r_en <= 1'b0;
		r_promiscuous <= 1'b0;
		mem_err <= 1'b0;
		//
		reset_rdfifo <= 1'b1;
		reset_wrfifo <= 1'b1;

		wr_baseaddr <= 0;
		wr_memsize  <= 0;
		wr_readptr  <= 0;

		rd_baseaddr <= 0;
		rd_memsize  <= 0;
		rd_writeptr <= 0;
	end else begin
		if (!r_en)
		begin
			reset_rdfifo <= 1'b1;
			reset_wrfifo <= 1'b1;
		end else if (!mem_err)
		begin
			reset_rdfifo <= 1'b0;
			reset_wrfifo <= 1'b0;
		end

		if (i_wb_stb && i_wb_we && !o_wb_stall && (&i_wb_sel))
		case(i_wb_addr)
		ADDR_CONTROL: begin
			r_promiscuous <= i_wb_data[0];
			r_en <= i_wb_data[1];	// ENABLE
			if (i_wb_data[2])
				mem_err <= 1'b0;
			end
		// ADDR_MYMAC1:
		// ADDR_MYMAC2:
		// ADDR_MYIP    = 5'h03,
		// Virtual packet FIFO configs
		// TX config (Read = read memory to network)
		// {{{
		ADDR_RDBASE: begin
			rd_baseaddr <= i_wb_data[BUSLSB +: AW];
			rd_writeptr <= i_wb_data[BUSLSB + AW-1:2];
			reset_rdfifo <= 1; end
		ADDR_RDSIZE: begin
			rd_memsize  <= i_wb_data[BUSLSB +: AW];
			reset_rdfifo <= 1;
			end
		ADDR_RDWPTR: rd_writeptr <= i_wb_data[BUSLSB + AW-1:2];
		// ADDR_RDRPTR: rd_readptr <= i_wb_data[BUSLSB + AW-1:2];
		// }}}
		// RX config (Write = network to write memory)
		// {{{
		ADDR_WRBASE: begin
			wr_baseaddr <= i_wb_data[BUSLSB +: AW];
			wr_readptr  <= i_wb_data[BUSLSB + AW-1:2];
			reset_wrfifo <= 1;
			end
		ADDR_WRSIZE: begin
			wr_memsize  <= i_wb_data[BUSLSB +: AW];
			reset_wrfifo <= 1;
			end
		// ADDR_WRWPTR: wr_writeptr;
		ADDR_WRRPTR: wr_readptr  <= i_wb_data[BUSLSB + AW-1:2];
		// }}}
		default: begin end
		endcase

		if (rd_baseaddr + rd_memsize > (1<<AW))
			reset_rdfifo <= 1;
		if (wr_baseaddr + wr_memsize > (1<<AW))
			reset_wrfifo <= 1;

		// Because of the way the bus multiplexer works, we can't
		// tell whether bus errors are due to TX or RX, so we reset
		// both on any error.
		if (o_dma_cyc && i_dma_err)
		begin
			reset_wrfifo <= 1'b1;
			reset_rdfifo <= 1'b1;
			mem_err <= 1'b1;
		end

		// if (rd_fifo_err) reset_rdfifo <= 1'b1;
	end

	assign	o_wb_stall = 1'b0;

	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= (i_wb_stb && !o_wb_stall);

	always @(posedge i_clk)
	if (i_reset && OPT_LOWPOWER)
		o_wb_data <= 0;
	else if ((!i_wb_stb || i_wb_we || (i_wb_sel == 0)) && OPT_LOWPOWER)
		o_wb_data <= 0;
	else begin
		o_wb_data <= 0;
		case(i_wb_addr)
		ADDR_CONTROL: begin
			// The first 3 of these bits are really required
			o_wb_data[0] <= r_promiscuous;
			o_wb_data[1] <= r_en;
			o_wb_data[2] <= mem_err;
			// The rest of these?  Not so much
			o_wb_data[3] <= reset_rdfifo;	// TX reset
			o_wb_data[4] <= reset_wrfifo;	// RX reset
			o_wb_data[5] <= o_tx_int;
			o_wb_data[6] <= o_rx_int;
			o_wb_data[7] <= rd_fifo_err;
			// And we've still got (32-8=) 24 unused/unassigned bits
			end
		ADDR_MYMAC1: o_wb_data[15:0] <= CPU_MAC[47:32];
		ADDR_MYMAC2: o_wb_data <= CPU_MAC[31:0];
		ADDR_MYIP:   o_wb_data <= CPU_IP;
		// ADDR_MYIPV61:
		// ADDR_MYIPV62:
		// ADDR_MYIPV63:
		// ADDR_MYIPV64:
		ADDR_RXDROPS: o_wb_data <= pkt_rxdrops;
		ADDR_RXPKTS:  o_wb_data <= pkt_rxcount;
		ADDR_TXPKTS:  o_wb_data <= pkt_txcount;
		// 5'h0b
		// 5'h0c
		// 5'h0d
		// 5'h0e
		// 5'h0f
		ADDR_RDBASE:  o_wb_data[BUSLSB +: AW] <= rd_baseaddr;
		ADDR_RDSIZE:  o_wb_data[BUSLSB +: AW] <= rd_memsize;
		ADDR_RDWPTR:  o_wb_data[AW+BUSLSB-1:2]<= rd_writeptr;
		ADDR_RDRPTR:  o_wb_data[AW+BUSLSB-1:2]<= rd_readptr;
		ADDR_WRBASE:  o_wb_data[BUSLSB +: AW] <= wr_baseaddr;
		ADDR_WRSIZE:  o_wb_data[BUSLSB +: AW] <= wr_memsize;
		ADDR_WRWPTR:  o_wb_data[AW+BUSLSB-1:2]<= wr_writeptr;
		ADDR_WRRPTR:  o_wb_data[AW+BUSLSB-1:2]<= wr_readptr;
		5'h18: o_wb_data <= {
				4'h0,
				1'b0, vfifo_wr.wr_outstanding,	// 8b
				1'b0, vfifo_wr.wr_state,	// 4b
				RX_VALID, RX_READY, RX_LAST,  RX_ABORT,
				my_valid, my_ready, my_last, my_abort,
				ipkt_valid, ipkt_ready, ipkt_last, ipkt_abort,
				wide_valid, wide_ready, wide_last,  wide_abort
			};
		5'h19: o_wb_data <= {
				4'h0,
				rd_wb_cyc, rd_wb_stb, rd_wb_ack, rd_wb_err,
				1'b0, vfifo_rd.rd_outstanding,	// 8b
				2'h0, vfifo_rd.rd_state,	// 4b
				TX_VALID, TX_READY, TX_LAST, ign_outw_abort,
				memfifo_valid, memfifo_ready, ign_mem_full, o_tx_int,
				mem_valid, memfifo_rd, mem_last,
					(rd_writeptr != rd_readptr)
			};
		5'h1a: o_wb_data <= { 16'h0,
				2'b0, ign_mem_fill,		// 8b
				2'b0, vfifo_rd.fifo_space };	// 8b
		5'h1b: o_wb_data[AW+$clog2(BUSDW/8)-1:0] <= vfifo_rd.return_len;
		default: o_wb_data <= 0;
		endcase
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Packet (statistic) counting
	// {{{
	assign	clear_counters = 0;

	always @(posedge i_clk)
	if (i_reset)
		mid_rxpkt <= 1'b0;
	else if (my_abort && (!my_valid || my_ready))
		mid_rxpkt <= 1'b0;
	else if (my_valid && my_ready)
		mid_rxpkt <= !my_last;
	else if (my_valid)
		mid_rxpkt <= 1'b1;

	always @(posedge i_clk)
	if (i_reset)
		pkt_rxdrops <= 0;
	else if (clear_counters || (i_wb_stb && i_wb_we && !o_wb_stall
				&& i_wb_addr == ADDR_RXDROPS && (&i_wb_sel)))
		pkt_rxdrops <= 0;
	else if (mid_rxpkt && (!my_valid || my_ready) && my_abort)
		pkt_rxdrops <= pkt_rxdrops + 1;

	always @(posedge i_clk)
	if (i_reset)
		pkt_rxcount <= 0;
	else if (clear_counters || (i_wb_stb && i_wb_we && !o_wb_stall
				&& i_wb_addr == ADDR_RXPKTS && (&i_wb_sel)))
		pkt_rxcount <= 0;
	else if (wide_valid && wide_ready && wide_last && !wide_abort)
		pkt_rxcount <= pkt_rxcount + 1;

	always @(posedge i_clk)
	if (i_reset)
		pkt_txcount <= 0;
	else if (clear_counters || (i_wb_stb && i_wb_we && !o_wb_stall
				&& i_wb_addr == ADDR_TXPKTS && (&i_wb_sel)))
		pkt_txcount <= 0;
	else if (TX_VALID && TX_READY && TX_LAST)
		pkt_txcount <= pkt_txcount + 1;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Drop any packets not addressed to us specifically
	// {{{

	checkmac #(
		.THIS_MAC(CPU_MAC),
		// .THIS_IPV4(CPU_IP),
		.PKTDW(PKTDW)
		// .OPT_LOWPOWER(OPT_LOWPOWER)
	) u_checkmac (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_en(!r_promiscuous),
		//
		.S_VALID(RX_VALID), .S_READY(RX_READY),
		.S_DATA(RX_DATA),   .S_BYTES(RX_BYTES),
		.S_LAST(RX_LAST),   .S_ABORT(RX_ABORT),
		//
		.M_VALID(my_valid), .M_READY(my_ready),
		.M_DATA(my_data),   .M_BYTES(my_bytes),
		.M_LAST(my_last),   .M_ABORT(my_abort)
		// }}}
	);

	// checkip
	// if ETHTYPE == ipv4 && !promiscuous && IP Addr != MY_IP
	//	then ABORT
	// IF (PKT[0][111:96] (IPv4 ETHTYPE) == 16'h0008) (Little endian)
	// THEN IF (PKT[0][119:116] != 4	(IPv4)
	// 	|| (PKT[1][119:112] != MY_IP[31:24]
	// 	|| (PKT[1][127:120] != MY_IP[23:16]
	// 	|| (PKT[2][  7:  0] != MY_IP[15: 8]
	// 	|| (PKT[2][ 15:  8] != MY_IP[ 7: 0]
	//  AND posn == 2
	//	ABORT = 1
	//

	// checkipv6
	// if ETHTYPE == ipv6 && !promiscuous && IPv6 Addr != MY_IPv6
	//	then ABORT
	// IF (PKT[0][111:96] (IPv6 ETHTYPE) == 16'hdd86)
	// THEN IF (PKT[0][119:116] != 6)	(IPv6)
	//	|| (PKT[2][ 55: 48] != MY_IPv6[127:120])	// Byte 24
	//	|| (PKT[1][ 63: 56] != MY_IPv6[127:112])
	//	|| (PKT[1][ 71: 64] != MY_IPv6[127:104])
	//	|| (PKT[1][ 79: 72] != MY_IPv6[127: 96])
	//	|| (PKT[1][ 87: 80] != MY_IPv6[127: 88])
	//	|| (PKT[1][ 95: 88] != MY_IPv6[127: 80])
	//	|| (PKT[1][103: 96] != MY_IPv6[127: 72])
	//	|| (PKT[1][111:104] != MY_IPv6[127: 64])
	//	|| (PKT[1][119:112] != MY_IPv6[ 63: 56])
	//	|| (PKT[1][127:120] != MY_IPv6[ 55: 48])
	//	|| (PKT[2][  7:  0] != MY_IPv6[ 47: 40])
	//	|| (PKT[2][ 15:  8] != MY_IPv6[ 39: 32])
	//	|| (PKT[2][ 23: 16] != MY_IPv6[ 31: 24])
	//	|| (PKT[2][ 31: 24] != MY_IPv6[ 23: 16])
	//	|| (PKT[2][ 39: 32] != MY_IPv6[ 15:  8])
	//	|| (PKT[2][ 47: 40] != MY_IPv6[  7:  0])

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming Width adjustment
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axinwidth #(
		.IW(PKTDW), .OW(BUSDW), .OPT_LITTLE_ENDIAN(1'b0)
	) u_inwidth (
		.ACLK(i_clk), .ARESETN(!i_reset && !reset_wrfifo),
		//
		.S_AXIN_VALID(my_valid), .S_AXIN_READY(my_ready),
		.S_AXIN_DATA(my_data), .S_AXIN_BYTES({
				((my_bytes==0) ? 1'b1:1'b0), my_bytes }),
		.S_AXIN_LAST(my_last), .S_AXIN_ABORT(my_abort),
		//
		.M_AXIN_VALID(ipkt_valid), .M_AXIN_READY(ipkt_ready),
		.M_AXIN_DATA(ipkt_data),
			.M_AXIN_BYTES({ ign_ipkt_msb, ipkt_bytes }),
		.M_AXIN_LAST(ipkt_last), .M_AXIN_ABORT(ipkt_abort)
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming data FIFO
	// {{{
	generate if (LGIFIFO > 1)
	begin : GEN_NETFIFO
		netfifo #(
			.BW(BUSDW+$clog2(BUSDW/8)), .LGFLEN(LGIFIFO)
		) u_prefifo (
			// {{{
			.S_AXI_ACLK(i_clk),
				.S_AXI_ARESETN(!i_reset && !reset_wrfifo),
			//
			.S_AXIN_VALID(ipkt_valid), .S_AXIN_READY(ipkt_ready),
			.S_AXIN_DATA({ ipkt_bytes, ipkt_data }),
			.S_AXIN_LAST(ipkt_last), .S_AXIN_ABORT(ipkt_abort),
			//
			.M_AXIN_VALID(wide_valid), .M_AXIN_READY(wide_ready),
			.M_AXIN_DATA({ wide_bytes, wide_data }),
			.M_AXIN_LAST(wide_last), .M_AXIN_ABORT(wide_abort)
			// }}}
		);
	end else begin : NO_NETFIFO
		assign	wide_valid = ipkt_valid;
		assign	ipkt_ready = wide_ready;
		assign	wide_data  = ipkt_data;
		assign	wide_bytes = ipkt_bytes;
		assign	wide_last  = ipkt_last;
		assign	wide_abort = ipkt_abort;
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// pktvfifowr: Everything else goes to memory for the CPU to pick it up
	// {{{

	pktvfifowr #(
		// {{{
		.BUSDW(BUSDW), .AW(AW), .LGPIPE(LGPIPE),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) vfifo_wr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_cfg_reset_fifo(reset_wrfifo), .i_cfg_mem_err(mem_err),
		.i_cfg_baseaddr(wr_baseaddr), .i_cfg_memsize(wr_memsize),
		.i_readptr(wr_readptr), .o_writeptr(wr_writeptr),
		//
		.S_VALID(wide_valid), .S_READY(wide_ready),
		.S_DATA(wide_data),   .S_BYTES(wide_bytes),
		.S_LAST(wide_last),   .S_ABORT(wide_abort),
		//
		.o_wb_cyc(wr_wb_cyc), .o_wb_stb(wr_wb_stb),
			.o_wb_we(wr_wb_we), .o_wb_addr(wr_wb_addr),
			.o_wb_data(wr_wb_data), .o_wb_sel(wr_wb_sel),
		.i_wb_stall(wr_wb_stall),
			.i_wb_ack(wr_wb_ack),
			// .i_dma_data(wr_wb_idata),
			.i_wb_err(wr_wb_err)
		// }}}
	);

	always @(posedge i_clk)
		o_rx_int <= (wr_readptr != wr_writeptr) || reset_wrfifo;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// pktvfiford: Issue packets the CPU is ready to send
	// {{{

	pktvfiford #(
		.BUSDW(BUSDW), .AW(AW), .LGPIPE(LGPIPE),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
		.OPT_LOWPOWER(OPT_LOWPOWER)
	) vfifo_rd (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_cfg_reset_fifo(reset_rdfifo), // .i_cfg_mem_err(mem_err),
		.i_cfg_baseaddr(rd_baseaddr), .i_cfg_memsize(rd_memsize),
		.o_readptr(rd_readptr), .i_writeptr(rd_writeptr),
		.o_fifo_err(rd_fifo_err),
		//
		.o_wb_cyc(rd_wb_cyc), .o_wb_stb(rd_wb_stb),
			.o_wb_we(rd_wb_we), .o_wb_addr(rd_wb_addr),
			.o_wb_data(rd_wb_data), .o_wb_sel(rd_wb_sel),
		.i_wb_stall(rd_wb_stall),
			.i_wb_ack(rd_wb_ack),
			.i_wb_data(rd_wb_idata),
			.i_wb_err(rd_wb_err),
		//
		.M_VALID(mem_valid), // .M_READY(mem_ready),
		.M_DATA(mem_data),   .M_BYTES(mem_bytes),
		.M_LAST(mem_last),   // .M_ABORT(mem_abort)
		.i_fifo_rd(memfifo_rd)
		// }}}
	);

	always @(posedge i_clk)
		o_tx_int <= (rd_readptr == rd_writeptr) || reset_rdfifo;


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Merge the two WB streams together
	// {{{

	wbmarbiter #(
		.DW(BUSDW), .AW(AW), .NIN(2), .LGFIFO(LGPIPE),
		.OPT_LOWPOWER(OPT_LOWPOWER)
	) u_wbmarbiter (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.s_cyc({   wr_wb_cyc,  rd_wb_cyc }),
		.s_stb({   wr_wb_stb,  rd_wb_stb }),
		.s_we({    wr_wb_we,   rd_wb_we  }),
		.s_addr({  wr_wb_addr, rd_wb_addr }),
		.s_data({  wr_wb_data, rd_wb_data }),
		.s_sel({   wr_wb_sel,  rd_wb_sel  }),
		.s_stall({ wr_wb_stall,rd_wb_stall  }),
		.s_ack({   wr_wb_ack,  rd_wb_ack  }),
		.s_idata({ wr_wb_idata,rd_wb_idata  }),
		.s_err({   wr_wb_err,  rd_wb_err  }),
		//
		.m_cyc(   o_dma_cyc   ),
		.m_stb(   o_dma_stb   ),
		.m_we(    o_dma_we    ),
		.m_addr(  o_dma_addr  ),
		.m_data(  o_dma_data  ),
		.m_sel(   o_dma_sel   ),
		.m_stall( i_dma_stall ),
		.m_ack(   i_dma_ack   ),
		.m_idata( i_dma_data ),
		.m_err(   i_dma_err   )
		// }}}
	);

	assign	o_debug= {
				(rd_wb_cyc || wr_wb_cyc),
				4'h0,
				vfifo_wr.wr_state,
				vfifo_rd.rd_state,
				o_dma_cyc, o_dma_stb, o_dma_we,
					i_dma_stall, i_dma_ack, i_dma_err,
				2'b0, wr_wb_cyc, wr_wb_stb, wr_wb_we,
					wr_wb_stall, wr_wb_ack, wr_wb_err,
				2'b0, rd_wb_cyc, rd_wb_stb, rd_wb_we,
					rd_wb_stall, rd_wb_ack, rd_wb_err
			};
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Return data FIFO
	// {{{

	sfifo #(
		.BW(BUSDW+$clog2(BUSDW/8)+1), .LGFLEN(LGOFIFO)
	) u_ackfifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || reset_rdfifo || rd_fifo_err),
		//
		.i_wr(mem_valid), .i_data({ mem_last, mem_bytes, mem_data }),
			.o_full(ign_mem_full), .o_fill(ign_mem_fill),
		.i_rd(memfifo_rd),
		//
		.o_data({ memfifo_last, memfifo_bytes, memfifo_data }),
			.o_empty(memfifo_empty)
		// }}}
	);

	assign	memfifo_valid = !memfifo_empty;
	assign	memfifo_rd = memfifo_valid && memfifo_ready;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing width adjustment
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		TX_ABORT <= 1'b0;
	else if (reset_rdfifo || rd_fifo_err)
		TX_ABORT <= 1'b1;
	else if (!TX_VALID || TX_READY)
		TX_ABORT <= 1'b0;

	axinwidth #(
		.IW(BUSDW), .OW(PKTDW), .OPT_LITTLE_ENDIAN(1'b0)
	) u_outwidth (
		// {{{
		.ACLK(i_clk), .ARESETN(!i_reset && !reset_rdfifo && !rd_fifo_err),
		//
		.S_AXIN_VALID( memfifo_valid),
		.S_AXIN_READY( memfifo_ready),
		.S_AXIN_DATA(  memfifo_data),
		.S_AXIN_BYTES({ (memfifo_bytes==0) ? 1'b1 : 1'b0,
						memfifo_bytes }),
		.S_AXIN_LAST(  memfifo_last),
		.S_AXIN_ABORT( 1'b0),
		//
		.M_AXIN_VALID(TX_VALID),
		.M_AXIN_READY(TX_READY),
		.M_AXIN_DATA( TX_DATA),
		.M_AXIN_BYTES({ ign_mbytes_lsb, TX_BYTES }),
		.M_AXIN_LAST( TX_LAST ),
		.M_AXIN_ABORT( ign_outw_abort)
		// }}}
	);
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, wr_wb_idata, ign_ipkt_msb, i_wb_cyc,
				i_wb_data,
				ign_mem_full, ign_mem_fill,
				ign_mbytes_lsb, ign_outw_abort };
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
	// }}}
endmodule
