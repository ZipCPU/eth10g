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
`default_nettype none
// }}}
module	cpunet #(
		parameter	DW = 512, AW = 30-$clog2(DW/8),
		parameter	PKTDW = 128,
		parameter [47:0]	CPU_MAC = 48'h1434_afa8_1234,
		// parameter [31:0] CPU_IP  ={ 8'd192, 8'd168, 8'd15, 8'd1 },
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter	LGFIFO = 5
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Control interface, for both virtual packet FIFOs
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[2:0]	i_wb_addr,
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
		output	wire				TX_ABORT,
		// }}}
		// DMA bus interface
		// {{{
		output	wire		o_dma_cyc, o_dma_stb, o_dma_we,
		output	wire [AW-1:0]	o_dma_addr,
		output	wire [DW-1:0]	o_dma_data,
		output	wire [DW/8-1:0]	o_dma_sel,
		input	wire		i_dma_stall,
		input	wire		i_dma_ack,
		input	wire [DW-1:0]	i_dma_data,
		input	wire		i_dma_err,
		// }}}
		output	wire		o_rx_int, o_tx_int
		// }}}
	);

	// Local declarations
	// {{{
	wire	MY_VALID, MY_READY, MY_LAST, MY_ABORT;
	wire	[PKTDW-1:0]		MY_DATA;
	wire	[$clog2(PKTDW/8)-1:0]	MY_BYTES;

	wire			rx_dma_cyc, rx_dma_stb, rx_dma_we;
	wire	[AW-1:0]	rx_dma_addr;
	wire	[DW-1:0]	rx_dma_data;
	wire	[(DW/8)-1:0]	rx_dma_sel;
	wire			rx_dma_stall, rx_dma_ack;
	wire	[DW-1:0]	rx_dma_idata;
	wire			rx_dma_err;

	wire			rx_wb_stall, rx_wb_ack;
	wire	[31:0]		rx_wb_data;

	wire			tx_dma_cyc, tx_dma_stb, tx_dma_we;
	wire	[AW-1:0]	tx_dma_addr;
	wire	[DW-1:0]	tx_dma_data;
	wire	[(DW/8)-1:0]	tx_dma_sel;
	wire			tx_dma_stall, tx_dma_ack;
	wire	[DW-1:0]	tx_dma_idata;
	wire			tx_dma_err;

	wire			tx_wb_stall, tx_wb_ack;
	wire	[31:0]		tx_wb_data;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Drop any packets not address to us specifically
	// {{{

	checkmac #(
		.THIS_MAC(CPU_MAC),
		// .THIS_IPV4(CPU_IP),
		.PKTDW(PKTDW)
		// .OPT_LOWPOWER(OPT_LOWPOWER)
	) u_checkmac (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.S_VALID(RX_VALID), .S_READY(RX_READY),
		.S_DATA(RX_DATA),   .S_BYTES(RX_BYTES),
		.S_LAST(RX_LAST),   .S_ABORT(RX_ABORT),
		//
		.M_VALID(MY_VALID), .M_READY(MY_READY),
		.M_DATA(MY_DATA),   .M_BYTES(MY_BYTES),
		.M_LAST(MY_LAST),   .M_ABORT(MY_ABORT)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// pkt2mem: Everything else goes to memory for the CPU to pick it up
	// {{{
	pkt2mem #(
		.DW(DW), .AW(AW),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.LGFIFO(LGFIFO)
	) u_rxpkt (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb && !i_wb_addr[2]),
			.i_wb_we(i_wb_we), .i_wb_addr(i_wb_addr[1:0]),
			.i_wb_data(i_wb_data), .i_wb_sel(i_wb_sel),
		.o_wb_stall(rx_wb_stall), .o_wb_ack(rx_wb_ack),
			.o_wb_data(rx_wb_data),
		//
		.S_AXIN_VALID(MY_VALID), .S_AXIN_READY(MY_READY),
		.S_AXIN_DATA(MY_DATA), .S_AXIN_BYTES(MY_BYTES),
		.S_AXIN_LAST(MY_LAST), .S_AXIN_ABORT(MY_ABORT),
		//
		.o_dma_cyc(rx_dma_cyc), .o_dma_stb(rx_dma_stb),
			.o_dma_we(rx_dma_we), .o_dma_addr(rx_dma_addr),
			.o_dma_data(rx_dma_data), .o_dma_sel(rx_dma_sel),
		.i_dma_stall(rx_dma_stall),
			.i_dma_ack(rx_dma_ack),
			.i_dma_data(rx_dma_idata),
			.i_dma_err(rx_dma_err),
		//
		.o_int(o_rx_int)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// mem2pkt: Issue packets the CPU is ready to send
	// {{{

	mem2pkt #(
		.DW(DW), .AW(AW),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
		// .OPT_LOWPOWER(OPT_LOWPOWER),
		.LGFIFO(LGFIFO)
	) u_txpkt (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb && i_wb_addr[2]),
			.i_wb_we(i_wb_we), .i_wb_addr(i_wb_addr[1:0]),
			.i_wb_data(i_wb_data), .i_wb_sel(i_wb_sel),
		.o_wb_stall(tx_wb_stall), .o_wb_ack(tx_wb_ack),
			.o_wb_data(tx_wb_data),
		//
		.o_dma_cyc(tx_dma_cyc), .o_dma_stb(tx_dma_stb),
			.o_dma_we(tx_dma_we), .o_dma_addr(tx_dma_addr),
			.o_dma_data(tx_dma_data), .o_dma_sel(tx_dma_sel),
		.i_dma_stall(tx_dma_stall),
			.i_dma_ack(tx_dma_ack),
			.i_dma_data(tx_dma_idata),
			.i_dma_err(tx_dma_err),
		//
		.M_AXIN_VALID(TX_VALID), .M_AXIN_READY(TX_READY),
		.M_AXIN_DATA(TX_DATA),   .M_AXIN_BYTES(TX_BYTES),
		.M_AXIN_LAST(TX_LAST),   .M_AXIN_ABORT(TX_ABORT),
		//
		.o_int(o_tx_int)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Merge the two WB streams together
	// {{{

	wbmarbiter #(
		.DW(DW), .AW(AW), .NIN(2), .LGFIFO(5),
		.OPT_LOWPOWER(OPT_LOWPOWER)
	) u_wbmarbiter (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.s_cyc({   tx_dma_cyc,  rx_dma_cyc }),
		.s_stb({   tx_dma_stb,  rx_dma_stb }),
		.s_we({    tx_dma_we,   rx_dma_we  }),
		.s_addr({  tx_dma_addr, rx_dma_addr }),
		.s_data({  tx_dma_data, rx_dma_data }),
		.s_sel({   tx_dma_sel,  rx_dma_sel  }),
		.s_stall({ tx_dma_stall,rx_dma_stall  }),
		.s_ack({   tx_dma_ack,  rx_dma_ack  }),
		.s_idata({ tx_dma_idata,rx_dma_idata  }),
		.s_err({   tx_dma_err,  rx_dma_err  }),
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

	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= (rx_wb_ack || tx_wb_ack);

	always @(posedge i_clk)
	if (rx_wb_ack)
		o_wb_data <= rx_wb_data;
	else if (tx_wb_ack)
		o_wb_data <= tx_wb_data;
	else
		o_wb_data <= 32'h0;

	assign	o_wb_stall = 1'b0;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, rx_wb_stall, tx_wb_stall };
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
	// }}}
endmodule
