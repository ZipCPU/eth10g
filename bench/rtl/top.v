////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	top.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:
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
`timescale 1 ns/1 fs
// }}}
module top;
	// Local declarations
	// {{{
	// Parameters
	parameter NUMBER_OF_CHANNEL = 4;
	parameter RECEIVED_PACKET_CNT = 1;   // 10 packets
	// [NUMBER_OF_CHANNEL-1:0]

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
	wire		net_to_fpga, fpga_to_net;
	wire		is_passed;
	wire		generator_complete;

	// The baud rate is given by 10GHz * 66/64, for a period of about 97ps.
	localparam	real	BAUD_RATE = 10e9 * 66/64;	// 10GHz * 66/64
	localparam	real	OVERSAMPLE_CLOCK_RATE = 8 * BAUD_RATE;
	// To get any real resolution here, we need femptosecond accuracy,
	//   so this is supposed to be about 12.121ps
	localparam realtime	CLOCK_PERIOD = 1.0 / BAUD_RATE;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock generation
	// {{{
	// initial begin ACLK = 1'b0; forever #(CLOCK_PERIOD/2) ACLK = !ACLK; end
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
	assign	fpga_to_net = net_to_fpga;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Scoreboard: Compare the packet sent with that received
	// {{{

	// If everything works, the packet sent should match the one
	// received.

	scoreboard
	score (
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
		.is_passed(is_passed),
		.crc_packets_rcvd(CRC_PKT_CNT),
		.model_packets_rcvd(MODEL_PKT_CNT)
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// VCD generator
	// {{{

	initial begin
		$dumpfile("top.vcd");
		$dumpvars(0, top);
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

endmodule
