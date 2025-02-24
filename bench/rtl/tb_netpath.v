////////////////////////////////////////////////////////////////////////////////
//
// Filename:	bench/rtl/tb_netpath.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Simulate a 10Gb network path from RX, through the CPU's packet
//		FIFO, and back to the network again.  This simulation is
//	necessary to verify this path will work, prior to hardware testing.
//	Other things can be done in hardware testing, but *only* if this
//	particular path is already reliable.
//
//	This is a top level test, although it doesn't include the top level
//	of the design.
//
// Creator:	Sukru Uzun.
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
`timescale 1 ns/1 fs
// }}}
module tb_netpath;
	// Local declarations
	// {{{
	// Parameters
	parameter RECEIVED_PACKET_CNT = 40;   // 40 packets
	localparam	BFM_AW = 5;	// Address bits to a CPUNET

	// clock and reset
	wire	SRC_CLK, SNK_CLK;
	wire	SRC_RESETN, SNK_RESETN;


	// script to (eth_model and crc_checker)
	wire		SCRIPT_M_VALID;
	wire		SCRIPT_M_READY, MODEL_TO_SCRIPT_READY,
				CRC_TO_SCRIPT_READY;
	wire		SCRIPT_M_LAST;
	wire		SCRIPT_M_ABORT;
	wire	[1:0]	SCRIPT_M_BYTES;
	wire	[31:0]	SCRIPT_M_DATA;
	wire		SCRIPT_TO_MODEL_FAULT;

	// eth_model to scoreboard
	wire		MODEL_TO_SCORE_VALID;
	wire		MODEL_TO_SCORE_READY;
	wire		MODEL_TO_SCORE_LAST;
	wire		MODEL_TO_SCORE_ABORT;
	wire	[2:0]	MODEL_TO_SCORE_BYTES;
	wire	[63:0]	MODEL_TO_SCORE_DATA;

	// crc_calculator to cdc
	wire		CRC_TO_CDC_READY;
	wire		CRC_TO_CDC_VALID;
	wire		CRC_TO_CDC_LAST;
	wire		CRC_TO_CDC_ABORT;
	wire	[2:0]	CRC_TO_CDC_BYTES;
	wire	[63:0]	CRC_TO_CDC_DATA;

	// cdc to scoreboard
	wire		CDC_TO_SCORE_READY;
	wire		CDC_TO_SCORE_VALID;
	wire		CDC_TO_SCORE_LAST;
	wire		CDC_TO_SCORE_ABORT;
	wire	[2:0]	CDC_TO_SCORE_BYTES;
	wire	[63:0]	CDC_TO_SCORE_DATA;

	// scoreboard
	wire	[5:0]	CRC_PKT_CNT;
	wire	[5:0]	MODEL_PKT_CNT;

	// others
	wire		net_to_fpga, fpga_to_net, ign_fpga_to_net;
	wire		is_passed, pkt_fail;
	wire		generator_complete;

	// The baud rate is given by 10GHz * 66/64, for a period of about 97ps.
	localparam	real	BAUD_RATE = 10e9 * 66/64;	// 10GHz * 66/64
	localparam	real	OVERSAMPLE_CLOCK_RATE = 8 * BAUD_RATE;
	// To get any real resolution here, we need femptosecond accuracy,
	//   so this is supposed to be about 12.121ps
	localparam realtime	CLOCK_PERIOD = 1.0 / BAUD_RATE;

	reg	wb_clk, phy_refclk, wb_reset, s_clk200;
	wire	phy_fault, fpga_tx_clk, fpga_rx_clk;
	wire	[31:0]	fpga_rx_data, fpga_tx_data;

	localparam	LGMEMSZ = 20;
	localparam	DW = 512, PKTDW=128;
	// Allocate one more bit than we have memory, so we can have a NULL
	// address space.  Remember, "AW" is the number of address bits
	// necessary to access a word of memory--not the number of address bits
	// necessary to access one octet of memory.
	localparam	AW = LGMEMSZ+1 - $clog2(DW/8);

	wire				led_link_up, led_activity;

	wire				RX_VALID, RX_READY, RX_LAST, RX_ABORT;
	wire	[PKTDW-1:0]		RX_DATA;
	wire	[$clog2(PKTDW/8)-1:0]	RX_BYTES;

	wire				TX_VALID, TX_READY, TX_LAST, TX_ABORT;
	wire	[PKTDW-1:0]		TX_DATA;
	wire	[$clog2(PKTDW/8)-1:0]	TX_BYTES;

	// CPUNET control bus connections
	// {{{
	reg			bfm_cyc, bfm_stb, bfm_we;
	reg	[BFM_AW-1:0]	bfm_addr;
	reg	[31:0]		bfm_data;
	reg	[3:0]		bfm_sel;
	wire			bfm_stall, bfm_ack;
	wire	[31:0]		bfm_idata;
	// }}}

	// CPUNET DMA bus connections
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

	// Clock period registers
	// {{{
	reg	[6:0]		tx_clk_count, rx_clk_count;
	reg	[15:0]		rc_clk_count;
	reg			tx_clk_trigger, rx_clk_trigger, rc_clk_trigger;
	realtime	rx_clk_timestamp, tx_clk_timestamp, rc_clk_timestamp;
	(* keep *) realtime	rx_clk_period, tx_clk_period, rc_clk_period;
	// }}}

	wire		p2m_int, m2p_int;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock generation
	// {{{
	// initial begin ACLK = 1'b0; forever #(CLOCK_PERIOD/2) ACLK = !ACLK; end
	parameter	realtime	WB_CLK_PERIOD = 10;
	parameter	realtime	PHY_REFCLK_PERIOD = 6.4;
	parameter	realtime	FAST_CLK_PERIOD = 5.0;

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

	// module instantiations
	// genvar i;
	// generate
	// for (i = 0; i < NUMBER_OF_CHANNEL; i = i + 1) begin : INSTANCE_LOOP

	////////////////////////////////////////////////////////////////////////
	//
	// Packet generator
	// {{{
	packet_generator
	u_script (
		.S_AXI_ACLK(SRC_CLK),
		.S_AXI_ARESETN(SRC_RESETN),
		//
		.M_VALID(SCRIPT_M_VALID),
		.M_READY(SCRIPT_M_READY),
		.M_DATA(SCRIPT_M_DATA),
		.M_BYTES(SCRIPT_M_BYTES),
		.M_LAST(SCRIPT_M_LAST),
		.M_ABORT(SCRIPT_M_ABORT),
		.M_FAULT(SCRIPT_TO_MODEL_FAULT),
		//
		.o_complete(generator_complete)
	);

	assign SCRIPT_M_READY = MODEL_TO_SCRIPT_READY; // CRC_TO_SCRIPT_READY && MODEL_TO_SCRIPT_READY;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CRC
	// {{{

	crc_calculator
	u_crc_calculator (
		.S_AXI_ACLK(SRC_CLK),
		.S_AXI_ARESETN(SRC_RESETN),
		// Inputs
		.S_AXIN_VALID(MODEL_TO_SCRIPT_READY && SCRIPT_M_VALID),
		.S_AXIN_READY(CRC_TO_SCRIPT_READY),
		.S_AXIN_DATA(SCRIPT_M_DATA),
		.S_AXIN_BYTES(SCRIPT_M_BYTES),
		.S_AXIN_LAST(SCRIPT_M_LAST),
		.S_AXIN_ABORT(SCRIPT_M_ABORT),
		// Outputs
		.M_AXIN_VALID(CRC_TO_CDC_VALID),
		.M_AXIN_READY(CRC_TO_CDC_READY),
		.M_AXIN_DATA(CRC_TO_CDC_DATA),
		.M_AXIN_BYTES(CRC_TO_CDC_BYTES),
		.M_AXIN_LAST(CRC_TO_CDC_LAST),
		.M_AXIN_ABORT(CRC_TO_CDC_ABORT)
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CDC: Move generated packets to the model's SINK clock domain
	// {{{

	axincdc #(
		.DW(64),	// Bits per beat
		.LGFIFO(4)	// Async FIFO size (log_2)
	) u_cdc (
		// {{{
		.S_CLK(SRC_CLK),
		.S_ARESETN(SRC_RESETN),
		.S_VALID(CRC_TO_CDC_VALID),
		.S_READY(CRC_TO_CDC_READY),
		.S_DATA(CRC_TO_CDC_DATA),
		.S_BYTES( CRC_TO_CDC_BYTES ),
		.S_ABORT(CRC_TO_CDC_ABORT),
		.S_LAST(CRC_TO_CDC_LAST),
		//
		.M_CLK(SNK_CLK),
		.M_ARESETN(SNK_RESETN),
		.M_VALID(CDC_TO_SCORE_VALID),
		.M_READY(CDC_TO_SCORE_READY),
		.M_DATA(CDC_TO_SCORE_DATA),
		.M_BYTES(CDC_TO_SCORE_BYTES),
		.M_LAST(CDC_TO_SCORE_LAST),
		.M_ABORT(CDC_TO_SCORE_ABORT)
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 10Gb Ethernet model
	// {{{

	// Take and transmit our packets, and receive the results

	tbenet
	eth_model (
		.i_cfg_bypass_scrambler(1'b0),
		//
		.S_CLK(SRC_CLK),
		.S_RESETn(SRC_RESETN),
		.S_VALID(SCRIPT_M_VALID),
		.S_READY(MODEL_TO_SCRIPT_READY),
		.S_DATA(SCRIPT_M_DATA),
		.S_BYTES(SCRIPT_M_BYTES),
		.S_FAULT(SCRIPT_TO_MODEL_FAULT),	// Src fault indicator
		.S_LAST(SCRIPT_M_LAST),
		//
		.o_tx(net_to_fpga),
		.i_rx(fpga_to_net),
		//
		.M_CLK(SNK_CLK),
		.M_RESETn(SNK_RESETN),
		.M_VALID(MODEL_TO_SCORE_VALID),
		.M_READY(MODEL_TO_SCORE_READY),
		.M_DATA(MODEL_TO_SCORE_DATA),
		.M_BYTES(MODEL_TO_SCORE_BYTES),
		.M_ABORT(MODEL_TO_SCORE_ABORT),
		.M_LAST(MODEL_TO_SCORE_LAST)
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Logic under test
	// {{{

	// Measure FPGA clock periods
	// {{{
	initial	{ rx_clk_trigger, rx_clk_count } = 0;
	always @(posedge fpga_rx_clk)
		{ rx_clk_trigger, rx_clk_count } <= rx_clk_count + 1;

	initial	{ tx_clk_trigger, tx_clk_count } = 0;
	always @(posedge fpga_tx_clk)
		{ tx_clk_trigger, tx_clk_count } <= tx_clk_count + 1;

	initial	{ rc_clk_trigger, rc_clk_count } = 0;
	always @(posedge eth_model.sample_clk)
		{ rc_clk_trigger, rc_clk_count } <= rc_clk_count + 1;

	always @(posedge fpga_rx_clk)
	if (rx_clk_trigger)
	begin
		rx_clk_period = ($time - rx_clk_timestamp)/128.0;
		rx_clk_timestamp = $time;
	end

	always @(posedge fpga_tx_clk)
	if (tx_clk_trigger)
	begin
		tx_clk_period = ($time - tx_clk_timestamp)/128.0;
		tx_clk_timestamp = $time;
	end

	always @(posedge eth_model.sample_clk)
	if (rc_clk_trigger)
	begin
		rc_clk_period = ($time - rc_clk_timestamp)/65536.0 * 64.0;
		rc_clk_timestamp = $time;
	end
	// }}}

	// First, the GTX transceivers
	// {{{
	// assign	fpga_to_net = net_to_fpga;

	xgtxphy #(
		.NDEV(1)
	) u_xgtxphy (
		// {{{
		.i_wb_clk(wb_clk),
		.o_phy_fault(phy_fault),
		//
		.S_CLK(  fpga_tx_clk),
		.S_DATA( fpga_tx_data),
		//
		.M_CLK(  fpga_rx_clk),
		.M_DATA( fpga_rx_data),
		//
		.i_refck_p( phy_refclk),
		.i_refck_n(!phy_refclk),
		.i_rx_p( net_to_fpga),
		.i_rx_n(!net_to_fpga),
		.o_tx_p(fpga_to_net),
		.o_tx_n(ign_fpga_to_net)
		// }}}
	);

	// }}}

	// Netpath, converts 66b GTX outputs to AXI Packet Streams
	// {{{

	netpath
	u_netpath (
		.i_rx_clk(fpga_rx_clk), .i_tx_clk(fpga_tx_clk),
		.i_reset_n(!wb_reset),
		.i_sys_clk(wb_clk), .i_fast_clk(s_clk200),
		.o_link_up(led_link_up), .o_activity(led_activity),
		//
		.i_phy_fault(phy_fault),
		// .i_raw_valid(fpga_rx_valid),
		.i_raw_data( fpga_rx_data),
		//
		// .i_raw_ready(fpga_tx_ready),
		.o_raw_data( fpga_tx_data),
		//
		.S_VALID(TX_VALID),
		.S_READY(TX_READY),
		.S_DATA( TX_DATA),
		.S_BYTES(TX_BYTES),
		.S_LAST( TX_LAST),
		.S_ABORT(TX_ABORT),
		//
		.M_VALID(RX_VALID),
		.M_READY(RX_READY),
		.M_DATA( RX_DATA),
		.M_BYTES(RX_BYTES),
		.M_LAST( RX_LAST),
		.M_ABORT(RX_ABORT)
	);

	// }}}

	// CPU based network packet FIFOs
	// {{{
	cpunet #(
		.BUSDW(DW), .AW(AW), .PKTDW(128)
	) u_cpunet (
		// {{{
		.i_clk(wb_clk), .i_reset(wb_reset),
		// Control port
		.i_wb_cyc(bfm_cyc), .i_wb_stb(bfm_stb), .i_wb_we(bfm_we),
			.i_wb_addr(bfm_addr),
			.i_wb_data(bfm_data), .i_wb_sel(bfm_sel),
		.o_wb_stall(bfm_stall), .o_wb_ack(bfm_ack),
			.o_wb_data(bfm_idata),
		// Incoming packets
		.RX_VALID(RX_VALID),
		.RX_READY(RX_READY),
		.RX_DATA( RX_DATA),
		.RX_BYTES(RX_BYTES),
		.RX_LAST( RX_LAST),
		.RX_ABORT(RX_ABORT),
		// Outgoing packets
		.TX_VALID(TX_VALID),
		.TX_READY(TX_READY),
		.TX_DATA( TX_DATA),
		.TX_BYTES(TX_BYTES),
		.TX_LAST( TX_LAST),
		.TX_ABORT(TX_ABORT),
		//
		// DMA interface
		.o_dma_cyc(net_cyc), .o_dma_stb(net_stb), .o_dma_we(net_we),
			.o_dma_addr(net_addr), .o_dma_data(net_data),
			.o_dma_sel(net_sel),
		.i_dma_stall(net_stall), .i_dma_ack(net_ack),
			.i_dma_data(net_idata), .i_dma_err(net_err),
		//
		.o_rx_int(p2m_int),
		.o_tx_int(m2p_int)
		// }}}
	);
	// }}}

	// No Wishbone arbiter required, already a part of cpunet
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
		@(posedge wb_clk);
		while(wb_reset)
			@(posedge wb_clk);

		bfm_write(5'h10, 32'h1 << LGMEMSZ);	// TX BASE
		bfm_write(5'h11, 32'h1 << LGMEMSZ);	// TX MEMLEN

		bfm_write(5'h14, 32'h1 << LGMEMSZ);	// RX BASE
		bfm_write(5'h15, 32'h1 << LGMEMSZ);	// RX MEMLEN

		bfm_write(5'h00, 32'h7);		// Promiscuous mode
		last_pointer = 32'h1 << LGMEMSZ;
		forever begin
			bfm_read(5'h16, read_data);
			if (read_data != last_pointer)
			begin
				// A new packet has arrived.  Tell the
				// MEM2PKT generator to forward it.
				last_pointer = read_data;
				bfm_write(5'h12, read_data);
			end
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Scoreboard: Compare the packet sent with that received
	// {{{

	// If everything works, the packet sent should match the one
	// received.

	scoreboard
	score (
		// {{{
		.S_AXI_ACLK(SNK_CLK),
		.S_AXI_ARESETN(SNK_RESETN),
		// model channel
		.MODEL_AXIN_VALID(MODEL_TO_SCORE_VALID),
		.MODEL_AXIN_READY(MODEL_TO_SCORE_READY),
		.MODEL_AXIN_BYTES(MODEL_TO_SCORE_BYTES),
		.MODEL_AXIN_DATA(MODEL_TO_SCORE_DATA),
		.MODEL_AXIN_LAST(MODEL_TO_SCORE_LAST),
		.MODEL_AXIN_ABORT(MODEL_TO_SCORE_ABORT),
		// crc_calculator channel
		.CRC_AXIN_VALID(CDC_TO_SCORE_VALID),
		.CRC_AXIN_READY(CDC_TO_SCORE_READY),
		.CRC_AXIN_BYTES(CDC_TO_SCORE_BYTES[2:0]),
		.CRC_AXIN_DATA(CDC_TO_SCORE_DATA),
		.CRC_AXIN_LAST(CDC_TO_SCORE_LAST && CDC_TO_SCORE_VALID),
		.CRC_AXIN_ABORT(CDC_TO_SCORE_ABORT),
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
		$dumpvars(0, tb_netpath);
	end
	// }}}

	always @(*)
	if (SRC_RESETN && SCRIPT_M_VALID
			&& MODEL_TO_SCRIPT_READY && !CRC_TO_SCRIPT_READY)
	begin
		assert(!SCRIPT_M_VALID || !MODEL_TO_SCRIPT_READY
						&& CRC_TO_SCRIPT_READY);
		$display("ERROR: CRC module is not ready.");
		$finish;
	end

	// (Pass) ending criteria
	initial begin
		wait(SNK_RESETN && generator_complete
				&& CRC_PKT_CNT == RECEIVED_PACKET_CNT
				&& MODEL_PKT_CNT == RECEIVED_PACKET_CNT);
		repeat (100)
			@(posedge SNK_CLK);  // wait for 100 clk

		$finish;
	end

	always @(posedge pkt_fail)
		$display("ERR: PACKET MISMATCH!");
endmodule
