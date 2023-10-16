////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tb_routecore.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Simulate a 10Gb network path from RX, through the router core,
//		and back to the network again.  This simulation is necessary to
//	verify this path will work, prior to hardware testing.
//
//	This is a top level test, although it doesn't include the top level
//	of the design.
//
// Creator:	Sukru Uzun.
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
`timescale 1 ns/1 fs
// }}}
module tb_routecore;
	// Parameters
	// {{{
	parameter RECEIVED_PACKET_CNT = 40;   // 40 packets
	parameter	NETH = 4;	// Number of ethernet connections
	localparam	BFM_AW = $clog2(NETH)+2; // Addr bits per route subcore

	parameter	realtime	WB_CLK_PERIOD = 10;
	parameter	realtime	PHY_REFCLK_PERIOD = 6.4;
	parameter	realtime	FAST_CLK_PERIOD = 5.0;

	// The baud rate is given by 10GHz * 66/64, for a period of about 97ps.
	localparam	real	BAUD_RATE = 10e9 * 66/64;	// 10GHz * 66/64
	localparam	real	OVERSAMPLE_CLOCK_RATE = 8 * BAUD_RATE;
	// To get any real resolution here, we need femptosecond accuracy,
	//   so this is supposed to be about 12.121ps
	localparam realtime	CLOCK_PERIOD = 1.0 / BAUD_RATE;

	localparam	LGMEMSZ = 20;
	localparam	DW = 512, PKTDW=128;
	// Allocate one more bit than we have memory, so we can have a NULL
	// address space.  Remember, "AW" is the number of address bits
	// necessary to access a word of memory--not the number of address bits
	// necessary to access one octet of memory.
	localparam	AW = LGMEMSZ+1 - $clog2(DW/8);

	// }}}

	// Local declarations
	// {{{
	genvar	geth;

	// clock and reset
	wire	[NETH-1:0]	SRC_CLK, SNK_CLK;
	wire	[NETH-1:0]	SRC_RESETN, SNK_RESETN;


	// script to (eth_model and crc_checker)
	wire	[NETH-1:0]	SCRIPT_M_VALID, SCRIPT_M_READY,
				MODEL_TO_SCRIPT_READY, CRC_TO_SCRIPT_READY;

	wire	[NETH-1:0]	SCRIPT_M_LAST;
	wire	[NETH-1:0]	SCRIPT_M_ABORT;
	wire	[NETH*2-1:0]	SCRIPT_M_BYTES;
	wire	[NETH*32-1:0]	SCRIPT_M_DATA;
	wire	[NETH-1:0]	SCRIPT_TO_MODEL_FAULT;

	// eth_model to scoreboard
	wire	[NETH-1:0]	DUT_TO_SCORE_VALID, DUT_TO_SCORE_READY,
				DUT_TO_SCORE_LAST, DUT_TO_SCORE_ABORT;
	wire	[NETH*3-1:0]	DUT_TO_SCORE_BYTES;
	wire	[NETH*64-1:0]	DUT_TO_SCORE_DATA;

	// crc_calculator to cdc
	wire		CRC_TO_CDC_READY;
	wire		CRC_TO_CDC_VALID;
	wire		CRC_TO_CDC_LAST;
	wire		CRC_TO_CDC_ABORT;
	wire	[2:0]	CRC_TO_CDC_BYTES;
	wire	[63:0]	CRC_TO_CDC_DATA;

	// cdc to scoreboard
	wire	[NETH-1:0]	MDL_TO_SCORE_VALID, MDL_TO_SCORE_READY,
				MDL_TO_SCORE_LAST,  MDL_TO_SCORE_ABORT;
	wire	[NETH*3-1:0]	MDL_TO_SCORE_BYTES;
	wire	[NETH*64-1:0]	MDL_TO_SCORE_DATA;

	// scoreboard
	wire	[5:0]		CRC_PKT_CNT, MODEL_PKT_CNT;

	// others
	wire	[NETH-1:0]	net_to_fpga, fpga_to_net, ign_fpga_to_net;
	wire			is_passed, pkt_fail;
	wire	[NETH-1:0]	generator_complete;

	reg			wb_clk, phy_refclk, wb_reset, s_clk200;
	wire	[NETH-1:0]	phy_fault, fpga_tx_clk, fpga_rx_clk;
	wire	[32*NETH-1:0]	fpga_rx_data, fpga_tx_data;

	wire	[NETH-1:0]	led_link_up, led_activity;

	wire	[NETH-1:0]		RX_VALID, RX_READY, RX_LAST, RX_ABORT;
	wire	[NETH*PKTDW-1:0]		RX_DATA;
	wire	[NETH*$clog2(PKTDW/8)-1:0]	RX_BYTES;

	wire	[NETH-1:0]		TX_VALID, TX_READY, TX_LAST, TX_ABORT;
	wire	[NETH*PKTDW-1:0]		TX_DATA;
	wire	[NETH*$clog2(PKTDW/8)-1:0]	TX_BYTES;

	// BFM WB control bus
	// {{{
	reg			bfm_cyc, bfm_stb, bfm_we;
	reg	[BFM_AW-1:0]	bfm_addr;
	reg	[31:0]		bfm_data;
	reg	[3:0]		bfm_sel;
	wire			bfm_stall, bfm_ack;
	wire	[31:0]		bfm_idata;
	// }}}

	// Packet Virtual FIFO bus connection(s)
	// {{{
	wire			net_cyc, net_stb, net_we,
				net_stall, net_ack;
	wire	[AW-1:0]	net_addr;
	wire	[DW-1:0]	net_data, net_idata;
	wire	[DW/8-1:0]	net_sel;

	wire			net_stall, net_ack, net_err;
	// }}}

	// Memory bus connections
	// {{{
	wire			mem_cyc, mem_stb, mem_we,
				mem_stall, mem_ack, mem_err;
	wire	[AW-1:0]	mem_addr;
	wire	[DW-1:0]	mem_data, mem_idata;
	wire	[DW/8-1:0]	mem_sel;
	// }}}

	reg	[31:0]	last_pointer, read_data;

	wire		p2m_int, m2p_int;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock generation
	// {{{
	initial	wb_clk = 1'b0;
	always
		#(WB_CLK_PERIOD/2) wb_clk = !wb_clk;

	initial	phy_refclk = 1'b0;
	always
		#(PHY_REFCLK_PERIOD/2) phy_refclk = !phy_refclk;

	initial	s_clk200 = 1'b0;
	always
		#(FAST_CLK_PERIOD/2) s_clk200 = !s_clk200;

	initial begin
		wb_reset <= 1;
		@(posedge wb_clk);
		@(posedge wb_clk);
		@(posedge wb_clk)
			wb_reset <= 0;
	end
	// }}}
	generate for (geth = 0; geth < NETH; geth=geth+1)
	begin : GEN_PER_ETHERNET_LINK

		////////////////////////////////////////////////////////////////
		//
		// Packet generator
		// {{{
		packet_generator #(
			.PKTFILE((geth == 0) ? "ethernet_packet.bin" : 0)
		) u_script (
			.S_AXI_ACLK(SRC_CLK[geth]),
			.S_AXI_ARESETN(SRC_RESETN[geth]),
			//
			.M_VALID(SCRIPT_M_VALID[geth]),
			.M_READY(SCRIPT_M_READY[geth]),
			.M_DATA(SCRIPT_M_DATA[32*geth +: 32]),
			.M_BYTES(SCRIPT_M_BYTES[2*geth +: 2]),
			.M_LAST(SCRIPT_M_LAST[geth]),
			.M_ABORT(SCRIPT_M_ABORT[geth]),
			.M_FAULT(SCRIPT_TO_MODEL_FAULT[geth]),
			//
			.o_complete(generator_complete[geth])
		);

		// CRC_TO_SCRIPT_READY && MODEL_TO_SCRIPT_READY;
		assign SCRIPT_M_READY = MODEL_TO_SCRIPT_READY;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// CRC : Switch 32->64b width, remove pkts w/ bad CRCs
		// {{{

		crc_calculator
		u_crc_calculator (
			.S_AXI_ACLK(SRC_CLK[geth]),
			.S_AXI_ARESETN(SRC_RESETN[geth]),
			// Inputs
			.S_AXIN_VALID(MODEL_TO_SCRIPT_READY[geth]
						&& SCRIPT_M_VALID[geth]),
			.S_AXIN_READY(CRC_TO_SCRIPT_READY[geth]),
			.S_AXIN_DATA(SCRIPT_M_DATA[32*geth +: 32]),
			.S_AXIN_BYTES(SCRIPT_M_BYTES[2*geth +: 2]),
			.S_AXIN_LAST(SCRIPT_M_LAST[geth]),
			.S_AXIN_ABORT(SCRIPT_M_ABORT[geth]),
			// Outputs
			.M_AXIN_VALID(CRC_TO_CDC_VALID[geth]),
			.M_AXIN_READY(CRC_TO_CDC_READY[geth]),
			.M_AXIN_DATA(CRC_TO_CDC_DATA[64*geth +: 64]),
			.M_AXIN_BYTES(CRC_TO_CDC_BYTES[3*geth +: 3]),
			.M_AXIN_LAST(CRC_TO_CDC_LAST[geth]),
			.M_AXIN_ABORT(CRC_TO_CDC_ABORT[geth])
		);
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// CDC: Move generated packets to the model's SINK clock domain
		// {{{

		axincdc #(
			.DW(64),	// Bits per beat
			.LGFIFO(4)	// Async FIFO size (log_2)
		) u_cdc (
			// {{{
			.S_CLK(SRC_CLK[geth]),
			.S_ARESETN(SRC_RESETN[geth]),
			.S_VALID(CRC_TO_CDC_VALID[geth]),
			.S_READY(CRC_TO_CDC_READY[geth]),
			.S_DATA(CRC_TO_CDC_DATA[64*geth +: 64]),
			.S_BYTES( CRC_TO_CDC_BYTES[3 * geth +: 3] ),
			.S_ABORT(CRC_TO_CDC_ABORT[geth]),
			.S_LAST(CRC_TO_CDC_LAST[geth]),
			//
			.M_CLK(SNK_CLK[(geth == 0) ? 3 : geth]),
			.M_ARESETN(SNK_RESETN[(geth == 0) ? 3 : geth]),
			.M_VALID(MDL_TO_SCORE_VALID[geth]),
			.M_READY(MDL_TO_SCORE_READY[geth]),
			.M_DATA(MDL_TO_SCORE_DATA[64*geth +: 64]),
			.M_BYTES(MDL_TO_SCORE_BYTES[3*geth +: 3]),
			.M_LAST(MDL_TO_SCORE_LAST[geth]),
			.M_ABORT(MDL_TO_SCORE_ABORT[geth])
			// }}}
		);
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// 10Gb Ethernet model
		// {{{

		// Take and transmit our packets, and receive the results

		tbenet
		eth_model (
			.i_cfg_bypass_scrambler(1'b0),
			//
			.S_CLK(SRC_CLK[geth]),
			.S_RESETn(SRC_RESETN[geth]),
			.S_VALID(SCRIPT_M_VALID[geth]),
			.S_READY(MODEL_TO_SCRIPT_READY[geth]),
			.S_DATA(SCRIPT_M_DATA[32 * geth +: 32]),
			.S_BYTES(SCRIPT_M_BYTES[2 * geth +: 2]),
			.S_FAULT(SCRIPT_TO_MODEL_FAULT[geth]),	// Src fault indicator
			.S_LAST(SCRIPT_M_LAST[geth]),
			//
			.o_tx(net_to_fpga[geth]),
			.i_rx(fpga_to_net[geth]),
			//
			.M_CLK(SNK_CLK[geth]),
			.M_RESETn(SNK_RESETN[geth]),
			.M_VALID(DUT_TO_SCORE_VALID[geth]),
			.M_READY(DUT_TO_SCORE_READY[geth]),
			.M_DATA(DUT_TO_SCORE_DATA[64*geth +: 64]),
			.M_BYTES(DUT_TO_SCORE_BYTES[3*geth +: 3]),
			.M_LAST(DUT_TO_SCORE_LAST[geth]),
			.M_ABORT(DUT_TO_SCORE_ABORT[geth])
		);
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Per-link FPGA Logic
		// {{{

		// First, the GTX transceivers
		// {{{

		xgtxphy #(
			.NDEV(1)
		) u_xgtxphy (
			// {{{
			.i_wb_clk(wb_clk),
			.o_phy_fault(phy_fault[geth]),
			//
			.S_CLK(  fpga_tx_clk[geth]),
			.S_DATA( fpga_tx_data[32 * geth +: 32]),
			//
			.M_CLK(  fpga_rx_clk[geth]),
			.M_DATA( fpga_rx_data[32 * geth +: 32]),
			//
			.i_refck_p( phy_refclk),
			.i_refck_n(!phy_refclk),
			.i_rx_p( net_to_fpga[geth]),
			.i_rx_n(!net_to_fpga[geth]),
			.o_tx_p(fpga_to_net[geth]),
			.o_tx_n(ign_fpga_to_net[geth])
			// }}}
		);

		// }}}

		// Netpath, converts 66b GTX outputs to AXI Packet Streams
		// {{{

		netpath
		u_netpath (
			.i_rx_clk(fpga_rx_clk[geth]),
			.i_tx_clk(fpga_tx_clk[geth]),
			.i_reset_n(!wb_reset),
			.i_sys_clk(wb_clk), .i_fast_clk(s_clk200),
			.o_link_up(led_link_up[geth]),
			.o_activity(led_activity[geth]),
			//
			.i_phy_fault(phy_fault[geth]),
			.i_raw_data( fpga_rx_data[geth * 32 +: 32]),
			//
			.o_raw_data( fpga_tx_data[geth * 32 +: 32]),
			//
			.S_VALID(TX_VALID[geth]),
			.S_READY(TX_READY[geth]),
			.S_DATA( TX_DATA[PKTDW * geth +: PKTDW]),
			.S_BYTES(TX_BYTES[$clog2(PKTDW/8)*geth +: $clog2(PKTDW/8)]),
			.S_LAST( TX_LAST[geth]),
			.S_ABORT(TX_ABORT[geth]),
			//
			.M_VALID(RX_VALID[geth]),
			.M_READY(RX_READY[geth]),
			.M_DATA( RX_DATA[PKTDW * geth +: PKTDW]),
			.M_BYTES(RX_BYTES[$clog2(PKTDW/8)*geth +: $clog2(PKTDW/8)]),
			.M_LAST( RX_LAST[geth]),
			.M_ABORT(RX_ABORT[geth])
		);

		// }}}
		// }}}
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// FPGA Core router
	// {{{
	routecore #(
		// {{{
		.NETH(NETH), .PKTDW(PKTDW), .BUSDW(DW),
		.DEF_BASEADDR({ 1'b1, {(LGMEMSZ-$clog2(DW/8)){1'b0}} }),
		.DEF_MEMSIZE( { 1'b1, {(LGMEMSZ-$clog2(DW/8)){1'b0}} })
		// }}}
	) u_routecore (
		// {{{
		.i_clk(wb_clk), .i_reset(wb_reset),
		.ETH_RESET({(NETH){1'b0}}),
		// Incoming packets from the PHY
		// {{{
		.RX_VALID(RX_VALID),
		.RX_READY(RX_READY),
		.RX_DATA( RX_DATA),
		.RX_BYTES(RX_BYTES),
		.RX_LAST( RX_LAST),
		.RX_ABORT(RX_ABORT),
		// }}}
		// Control interface
		// {{{
		.i_ctrl_cyc(bfm_cyc), .i_ctrl_stb(bfm_stb), .i_ctrl_we(bfm_we),
		.i_ctrl_addr(bfm_addr),
			.i_ctrl_data(bfm_data),
			.i_ctrl_sel(bfm_sel),
		.o_ctrl_stall(bfm_stall),
		.o_ctrl_ack(bfm_ack), .o_ctrl_data(bfm_idata),
		// }}}
		// VFIFO interface
		// {{{
		.o_vfifo_cyc(net_cyc), .o_vfifo_stb(net_stb),
			.o_vfifo_we(net_we),
		.o_vfifo_addr(net_addr),
			.o_vfifo_data(net_data),
			.o_vfifo_sel(net_sel),
		.i_vfifo_stall(net_stall),
		.i_vfifo_ack(net_ack), .i_vfifo_data(net_idata),
		.i_vfifo_err(1'b0),
		// }}}
		// Routed packets, headed back to the PHY
		// {{{
		.TX_VALID(TX_VALID),
		.TX_READY(TX_READY),
		.TX_DATA( TX_DATA),
		.TX_BYTES(TX_BYTES),
		.TX_LAST( TX_LAST),
		.TX_ABORT(TX_ABORT)
		// }}}
		// }}}
	);


	// No Wishbone arbiter required, already a part of the core router
	// {{{
	assign	mem_cyc  = net_cyc;
	assign	mem_stb  = net_stb;
	assign	mem_we   = net_we;
	assign	mem_addr = net_addr;
	assign	mem_data = net_data;
	assign	mem_sel  = net_sel;
	//
	assign	net_stall= mem_stall;
	assign	net_ack  = mem_ack;
	assign	net_idata= mem_idata;
	assign	net_err  = mem_err;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The memory, required by the virtual packet FIFOs, and *SHARED*
	// {{{
	memdev #(
		.LGMEMSZ(LGMEMSZ), .DW(DW)
	) u_mem (
		.i_clk(wb_clk), .i_reset(wb_reset),
		//
		.i_wb_cyc(mem_cyc),     .i_wb_stb(mem_stb),
		.i_wb_we(mem_we),       .i_wb_addr(mem_addr[LGMEMSZ-$clog2(DW/8)-1:0]),
		.i_wb_data(mem_data),   .i_wb_sel(mem_sel),
		//
		.o_wb_stall(mem_stall), .o_wb_ack(mem_ack),
		.o_wb_data(mem_idata)
	);

	assign	mem_err = 1'b0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// A BFM to drive the WB and set up the virtual network FIFOs
	// {{{
	task	bfm_write(input [BFM_AW-1:0] addr, input [31:0] data);
		// {{{
		reg	ackd;
	begin
		ackd = 1'b0;

		// We assume we come into here with CYC and STB low
		@(posedge wb_clk)
		begin
			bfm_cyc  <= 1'b1;
			bfm_stb  <= 1'b1;
			bfm_we   <= 1'b1;
			bfm_addr <= addr;
			bfm_data <= data;
			bfm_sel  <= 4'hf;
		end

		do begin
			// Force the non-blocking assignments to take effect
			@(negedge wb_clk);

			// Clear the strobe if and when we can
			@(posedge wb_clk)
			begin
				if (!bfm_stall)
					bfm_stb <= 1'b0;
				if (bfm_ack)
					ackd <= 1'b1;
			end
		end while(bfm_stb);

		while(!ackd)
		begin
			@(posedge wb_clk)
			if (bfm_ack)
				ackd <= 1'b1;
		end

		@(posedge wb_clk)
			bfm_cyc <= 1'b0;
	end endtask
	// }}}

	task	bfm_read(input [BFM_AW-1:0] addr, output [31:0] data);
		// {{{
		reg	ackd;
	begin
		ackd = 1'b0;

		// We assume we come into here with CYC and STB low
		@(posedge wb_clk)
		begin
			bfm_cyc  <= 1'b1;
			bfm_stb  <= 1'b1;
			bfm_we   <= 1'b0;
			bfm_addr <= addr;
			bfm_data <= 32'h0;
			bfm_sel  <= 4'hf;
		end

		do begin
			// Force the non-blocking assignments to take effect
			@(negedge wb_clk);

			// Clear the strobe if and when we can
			@(posedge wb_clk)
			begin
				if (!bfm_stall)
					bfm_stb <= 1'b0;
				if (bfm_ack)
				begin
					ackd <= 1'b1;
					data <= bfm_idata;
				end
			end
		end while(bfm_stb);

		while(!ackd)
		begin
			@(posedge wb_clk)
			if (bfm_ack)
			begin
				ackd <= 1'b1;
				data <= bfm_idata;
			end
		end

		@(posedge wb_clk)
			bfm_cyc <= 1'b0;
	end endtask
	// }}}

	initial	begin
		bfm_cyc  = 1'b0;
		bfm_stb  = 1'b0;
		bfm_we   = 1'b0;
		bfm_addr = 3'b0;
		bfm_data = 32'b0;
		bfm_sel  = 4'hf;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Scoreboard: Compare the packet sent with that received
	// {{{

	// If everything works, the packet sent should match the one
	// received.

	wire	score_board_ready_model, score_board_ready_dut;

	assign	DUT_TO_SCORE_READY = {score_board_ready_model,
						{(NETH-1){1'b1}} };
	assign	MDL_TO_SCORE_READY = {{(NETH-1){1'b1}}, score_board_ready_dut};

	scoreboard
	score (
		// {{{
		.S_AXI_ACLK(SNK_CLK[NETH-1]),
		.S_AXI_ARESETN(SNK_RESETN[NETH-1]),
		// DUT channel, coming through the simulated FPGA components
		.MODEL_AXIN_VALID(DUT_TO_SCORE_VALID[NETH-1]),
		.MODEL_AXIN_READY(score_board_ready_model),
		.MODEL_AXIN_BYTES(DUT_TO_SCORE_BYTES[(NETH-1)*3 +: 3]),
		.MODEL_AXIN_DATA(DUT_TO_SCORE_DATA[(NETH-1)*64 +: 64]),
		.MODEL_AXIN_LAST(DUT_TO_SCORE_LAST[NETH-1]),
		.MODEL_AXIN_ABORT(DUT_TO_SCORE_ABORT[NETH-1]),
		// crc_calculator channel from our packet generator
		.CRC_AXIN_VALID(MDL_TO_SCORE_VALID[0]),
		.CRC_AXIN_READY(score_board_ready_dut),
		.CRC_AXIN_BYTES(MDL_TO_SCORE_BYTES[3*0 +: 3]),
		.CRC_AXIN_DATA(MDL_TO_SCORE_DATA[64*0 +: 64]),
		.CRC_AXIN_LAST(MDL_TO_SCORE_LAST[0]),
		.CRC_AXIN_ABORT(MDL_TO_SCORE_ABORT[0]),
		//
		.is_passed(is_passed), .pkt_fail(pkt_fail),
		.crc_packets_rcvd(CRC_PKT_CNT),
		.model_packets_rcvd(MODEL_PKT_CNT)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// VCD generator
	// {{{

	initial begin
		$dumpfile("top.vcd");
		$dumpvars(0, tb_routecore);
	end
	// }}}

	always @(*)
	if (|(SRC_RESETN & SCRIPT_M_VALID
			& MODEL_TO_SCRIPT_READY & ~CRC_TO_SCRIPT_READY))
	begin
		assert(~SCRIPT_M_VALID | ~MODEL_TO_SCRIPT_READY
						& CRC_TO_SCRIPT_READY);
		$display("ERROR: CRC module is not ready.");
		$finish;
	end

	// (Pass) ending criteria
	initial begin
		wait((&SNK_RESETN) && (&generator_complete)
				&& CRC_PKT_CNT   == RECEIVED_PACKET_CNT
				&& MODEL_PKT_CNT == RECEIVED_PACKET_CNT);
		repeat (100)
			@(posedge SNK_CLK[0]);  // wait for 100 clk cycles

		$finish;
	end

	always @(posedge pkt_fail)
		$display("ERR: PACKET MISMATCH!");
endmodule
