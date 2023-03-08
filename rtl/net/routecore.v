////////////////////////////////////////////////////////////////////////////////
//
// Filename:	routecore.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is intended to be the core of the network router: the
//		routing table.  When a packet is received, from any interface,
//	it is registered in this table together with the interface it comes
//	from.  Then, when we later want to transmit a packet, the table can be
//	queried for which port the given MAC address was last seen on.
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
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module routecore #(
		// {{{
		// parameter [0:0]	OPT_SKIDBUFFER   = 1'b0,
		// parameter [0:0]	OPT_LOWPOWER     = 1'b0
		// parameter [0:0]	OPT_DEFBROADCAST = 1'b0
		// parameter [0:0]	OPT_ONE_TO_MANY  = 1'b0
		parameter	NETH = 4,	// Number of incoming eth ports
		// DW is the bits per clock cycle or beat.  It is also the
		// bus data width.  Any/all width conversions take place
		// outside of this module.  In order to properly cross clock
		// domains, DW must be greater than the original.  So if the
		// interface will generate (roughly) 32'bits per clock, DW must
		// be at least 64-bits per clock.
		parameter	DW = 64,	// Bits per clock cycle
		// parameter 	BROADCAST_PORT = NETH,
		// parameter 	DEFAULT_PORT = BROADCAST_PORT,
		// parameter	LGTBL = 6,	// Log_2(NTBL entries)
		// localparam	NTBL = (1<<LGTBL), // Number of table entries
		// parameter	LGTIMEOUT = 64-MACW-1,
		parameter	MACW = 48,	// Bits in a MAC address
		parameter	LGROUTETBL = 6,
		parameter	LGROUTE_TIMEOUT = 24
		// }}}
	) (
		// {{{
		input	wire				i_clk, i_reset,
		// We have only one clock--the bus clock.  All CDCs take
		// place on the way in and on the way out to allow us to
		// work in this one clock domain
		// input	wire	[NETH-1:0]		ETH_CLK,
		//
		// It is possible that we might turn off various interfaces.
		// When an interface is off, that bit in ETH_RESET will be one.
		input	wire	[NETH-1:0]		ETH_RESET,
		// Incoming packets from all interfaces
		// {{{
		input	wire	[NETH-1:0]		RX_VALID,
		output	wire	[NETH-1:0]		RX_READY,
		input	wire	[NETH*DW-1:0]		RX_DATA,
		input	wire	[NETH*$clog2(DW)-1:0]	RX_BYTES,
		input	wire	[NETH-1:0]		RX_LAST,
		input	wire	[NETH-1:0]		RX_ABORT,
		// }}}
		// Outgoing packets
		// {{{
		output	wire	[NETH-1:0]		TX_VALID,
		input	wire	[NETH-1:0]		TX_READY,
		output	wire	[NETH*DW-1:0]		TX_DATA,
		output	wire	[NETH*$clog2(DW)-1:0]	TX_BYTES,
		output	wire	[NETH-1:0]		TX_LAST,
		output	wire	[NETH-1:0]		TX_ABORT,
		// }}}
		// }}}
	);

	wire	[NETH-1:0]		tomem_valid, tomem_ready;
	wire	[NETH*DW-1:0]		tomem_data;
	wire	[NETH*$clog2(DW)-1:0]	tomem_bytes;
	wire	[NETH-1:0]		tomem_abort;
	wire	[NETH-1:0]		tomem_last;

	wire				rxtbl_valid[NETH*NETH];
	wire				rxtbl_ready[NETH*NETH];
	wire				rxtbl_data[NETH*NETH * MACW];

	wire	[NETH*NETH-1:0]		txx_valid, txx_ready;
	wire	[NETH*NETH*DW-1:0]	txx_data;
	wire [NETH*NETH*$clog2(DW)-1:0]	txx_bytes;
	wire	[NETH*NETH-1:0]		txx_last, txx_abort;

	generate for (geth=0; geth < NETH; geth = geth+1)
	begin : GEN_INTERFACES
		localparam [NETH-1:0]	THIS_PORT = (1<<geth);
		wire			smac_valid, smac_ready;
		wire	[MACW-1:0]	smac_data;

		wire			mmout_valid, mmout_ready,
					mmout_abort, mmout_last;
		wire	[DW-1:0]	mmout_data;
		wire [$clog2(DW)-1:0]	mmout_bytes;

		integer			iport;
		reg	[NETH-1:0]	remap_valid;
		wire	[NETH-1:0]	remap_ready;
		reg	[NETH*MACW-1:0]	remap_data;

		wire			lkup_request, lkup_valid;
		wire	[MACW-1:0]	lkup_mac;
		wire	[NETH-1:0]	lkup_port;

		// Grab packet MACs for the router
		// {{{
		rxgetsrcmac #(
			.DW(DW), .MACW(MACW)
		) u_rxgetsrcmac (
			// {{{
			.i_clk(i_clk),
			.i_reset(i_reset || ETH_RESET[geth]),
			//
			.S_VALID(RX_VALID[geth]),
			.S_READY(RX_READY[geth]),
			.S_DATA( RX_DATA[geth * DW +: DW]),
			.S_BYTES(RX_BYTES[geth * $clog2(DW) +: $clog2(DW)]),
			.S_ABORT(RX_ABORT[geth]),
			.S_LAST( RX_LAST[geth]),
			//
			.M_VALID(tomem_valid[geth]),
			.M_READY(tomem_ready[geth]),
			.M_DATA( tomem_data[geth * DW +: DW]),
			.M_BYTES(tomem_bytes[geth * $clog2(DW) +: $clog2(DW)]),
			.M_ABORT(tomem_abort[geth]),
			.M_LAST( tomem_last[geth]),
			//
			.TBL_VALID(smac_valid),
			.TBL_READY(smac_ready),
			.TBL_SRCMAC(smac_data)
			// }}}
		);
		// }}}

		// smac->rxtbl: Broadcast Rx MACs to each channel's router
		// {{{
		axisbroadcast #(
			.C_AXIS_DATA_WIDTH(MACW), .NM(NETH)
		) u_rxtbl_broadcast (
			// {{{
			.S_AXI_ACLK(i_clk),
			.S_AXI_ARESETN(i_reset || ETH_RESET[geth]),
			//
			.S_AXIS_TVALID(smac_valid),
			.S_AXI_TREADY(smac_ready),
			.S_AXI_TDATA(smac_data),
			//
			.M_AXI_TVALID(rxtbl_valid[geth * NETH +: NETH]),
			.M_AXI_TREADY(rxtbl_ready[geth * NETH +: NETH] | ETH_RESET),
			.M_AXI_TDATA(rxtbl_data[geth * MACW * NETH +: MACW * NETH])
			// }}}
		);
		// }}}

		// All packets go to memory: tomem -> (dma_wb) -> mmout
		// {{{
		pktvfifo #(
			.AW(AW),	// Bus address width
			.DW(DW)		// Bus width
		) u_pktvfifo (
			.i_clk(i_clk),
			.i_reset(i_reset || ETH_RESET[geth]),
			// Bus control
			// {{{
			.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb
				&& i_wb_addr[2 +: $clog2(NETH)] == geth),
			.i_wb_we(i_wb_we), .i_wb_addr(i_wb_addr[1:0]),
			.i_wb_data(i_wb_data), .i_wb_sel(i_wb_sel),
			.o_wb_stall(pkt2m_stall[geth]),
			.o_wb_ack(pkt2m_ack[geth]),
			.o_wb_data(pkt2m_data[DW*geth +: DW]),
			// }}}
			// Incoming packet
			// {{{
			.S_VALID(tomem_valid[geth]),
			.S_READY(tomem_ready[geth]),
			.S_DATA( tomem_data[geth * DW +: DW]),
			.S_BYTES(tomem_bytes[geth * $clog2(DW) +: $clog2(DW)]),
			.S_ABORT(tomem_abort[geth]),
			.S_LAST( tomem_last[geth]),
			// }}}
			// DMA bus interface
			// {{{
			.o_wb_cyc(dma_cyc[geth]),
			.o_wb_stb(dma_stb[geth]),
			.o_wb_we(dma_we[geth]),
			.o_wb_addr(dma_addr[geth]),
			.o_wb_data(dma_data[geth]),
			.o_wb_sel(dma_sel[geth]),
			.i_wb_stall(dma_stall[geth]),
			.i_wb_ack(dma_ack[geth]),
			.i_wb_data(dma_idata[DW*geth +: DW]),
			.i_wb_err(dma_err[geth]),
			// This needs to go to a crossbar next ...
			// }}}
			// Outgoing packet
			// {{{
			.M_VALID(mmout_valid),
			.M_READY(mmout_ready),
			.M_DATA( mmout_data),
			.M_BYTES(mmout_bytes),
			.M_ABORT(mmout_abort),
			.M_LAST( mmout_last)
			// }}}
		);
		// }}}

		// mmout->rtd, On return from memory, lookup the destinations
		// {{{
		txgetports #(
			// {{{
			// .OPT_SKIDBUFFER
			// .OPT_LOWPOWER
			.NETH(NETH),
			.DW(DW)
			// .MACW(48)
			// }}}
		) u_txgetports (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.S_VALID(mmout_valid), .S_READY(mmout_ready),
			.S_DATA(mmout_data), .S_BYTES(mmout_bytes),
			.S_LAST(mmout_last), .S_ABORT(mmout_abort),
			//
			//
			.TBL_REQUEST(lkup_request), .TBL_VALID(lkup_valid),
			.TBL_MAC(lkup_mac), .TBL_PORT(lkup_port & ~THIS_PORT),
			//
			.M_VALID(rtd_valid), .M_READY(rtd_ready),
			.M_DATA(rtd_data), .M_BYTES(rtd_bytes),
			.M_LAST(rtd_last), .M_ABORT(rtd_abort),
			.M_PORT(rtd_port)
			//
			// }}}
		);
		// }}}

		// rtd->txx Broadcast our packet to all interested ports
		// {{{
		rtdbroadcast #(
			.C_AXIS_DATA_WIDTH(MACW), .NM(NETH)
		) u_rtdbroadcast (
			// {{{
			.S_AXI_ACLK(i_clk),
			.S_AXI_ARESETN(!i_reset),
			//
			.i_cfg_active(~ETH_RESET);
			// rtd_*, packet with routing
			// {{{
			.S_AXIN_VALID(rtd_valid),
			.S_AXIN_READY(rtd_ready),
			.S_AXIN_DATA(rtd_data),
			.S_AXIN_PORT(rtd_port),
			.S_AXIN_BYTES(rtd_bytes),
			.S_AXIN_LAST(rtd_last),
			.S_AXIN_ABORT(rtd_abort),
			// }}}
			// txx_*
			// {{{
			.M_AXIN_VALID(txx_valid[geth * NETH +: NETH]),
			.M_AXIN_READY(txx_ready[geth * NETH +: NETH] | ETH_RESET),
			.M_AXIN_DATA(txx_data[geth * DW * NETH +: DW * NETH]),
			.M_AXIN_BYTES(txx_bytes[geth * $clog2(DW) * NETH
						+: $clog2(DW) * NETH]),
			.M_AXIN_LAST(txx_last[geth * NETH +: NETH])
			.M_AXIN_ABORT(txx_abort[geth * NETH +: NETH])
			// }}}
			// }}}
		);
		// }}}

		// Arbitrate from among packets from other ports
		// {{{
		integer				iport;
		reg	[NETH-1:0]		prearb_valid, prearb_ready;
		wire	[NETH-1:0]		prearb_ready;
		reg	[NETH*DW-1:0]		prearb_data;
		reg	[NETH*$clog2(DW)-1:0]	prearb_bytes;
		reg	[NETH-1:0]		prearb_last, prearb_abort;

		always @(*)
		for(iport=0; iport<NETH; iport=iport+1)
		begin
			prearb_valid[iport] = txx_valid[geth * NETH+iport];
			txx_ready[geth*NETH+iport] = prearb_ready[iport];
			prearb_data[iport * DW +: DW]
				 = txx_data[(geth*NETH+iport)*DW +: DW];
			prearb_bytes[iport * $clog2(DW) +: $clog2(DW)]
				 = txx_bytes[(geth*NETH+iport)*$clog2(DW) +: $clog2(DW)];
			prearb_last[iport]  = txx_last[geth*NETH+iport];
			prearb_abort[iport] = txx_data[geth*NETH+iport];
		end

		axinarbiter #(
			.DW(DW),
			.NETH(NETH)
		) u_txarbiter (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.S_AXIN_VALID(prearb_valid),
			.S_AXIN_READY(prearb_ready),
			.S_AXIN_DATA( prearb_data),
			.S_AXIN_BYTES(prearb_bytes),
			.S_AXIN_LAST( prearb_last),
			.S_AXIN_ABORT(prearb_abort),
			//
			.M_AXIN_VALID(TX_VALID[geth]),
			.M_AXIN_READY(TX_READY[geth]),
			.M_AXIN_DATA( TX_DATA[ geth*DW +: DW]),
			.M_AXIN_BYTES(TX_BYTES[geth*$clog2(DW) +: $clog2(DW)]),
			.M_AXIN_LAST( TX_LAST[ geth]),
			.M_AXIN_ABORT(TX_ABORT[geth])
			// }}}
		);
		// }}}

		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		// The router table itself
		// {{{
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////

		always @(*)
		for(iport=0; iport<NETH; iport=iport+1)
		begin
			remap_valid[iport] = rxtbl_valid[geth * NETH+iport];
			rxtbl_ready[geth*NETH+iport] = remap_ready[iport];
			remap_data[iport * MACW +: MACW]
				 = rxtbl_data[(geth*NETH+iport)*MACW +: MACW];
		end

		rxroutetbl #(
			// {{{
			.NETH(NETH),
			.BROADCAST_PORT({(NETH){1'b1}} & ~(1<<gk)),
			// .DEFAULT_PORT(NETH),
			.LGTBL(LGROUTETBL),
			.LGTIMEOUT(LGROUTE_TIMEOUT),
			.MACW(MACW)
			// }}}
		) u_routetbl (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.RX_VALID(remap_valid),
			.RX_READY(remap_ready),
			.RX_SRCMAC(remap_data),

			.TX_VALID(lkup_request),
			.TX_READY(lkup_valid),
			.TX_DSTMAC(lkup_dstmac),
			.TX_PORT(lkup_port)
			// }}}
		);

		// }}}
	end endgenerate

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
