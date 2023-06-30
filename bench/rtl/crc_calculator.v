////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	crc_calculator.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Converts a packet from 32-bits wide to 64bits, and then checks
//		the CRC.  Packets with failing CRCs are aborted.
//
// Creator:	Sukru Uzun
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
`timescale 1 ns/1 ps
// }}}
module crc_calculator (
		// {{{
		// clk, reset
		input wire S_AXI_ACLK,
		input wire S_AXI_ARESETN,
		
		// Inputs
		input wire S_AXIN_VALID,
		output wire S_AXIN_READY,
		input wire [31:0] S_AXIN_DATA,
		inout wire [1:0] S_AXIN_BYTES,
		input wire S_AXIN_LAST,
		input wire S_AXIN_ABORT,
		
		// Outputs
		output wire M_AXIN_VALID,
		input  wire M_AXIN_READY,
		output wire [63:0] M_AXIN_DATA,
		output wire [2:0] M_AXIN_BYTES,
		output wire M_AXIN_LAST,
		output wire M_AXIN_ABORT
		// }}}
	);

	// Local declarations
	// {{{
	wire	[3:0] M_BYTES;

	// width_to_crc
	wire	WIDTH_TO_CRC_VALID;
	wire	WIDTH_TO_CRC_READY;
	wire	[63:0] WIDTH_TO_CRC_DATA;
	wire	[3:0] WIDTH_TO_CRC_BYTES;
	wire	WIDTH_TO_CRC_LAST;
	wire	WIDTH_TO_CRC_ABORT;

	// crc_to_fifo
	wire	CRC_TO_FIFO_VALID;
	wire	CRC_TO_FIFO_READY;
	wire	[63:0] CRC_TO_FIFO_DATA;
	wire	[3:0] CRC_TO_FIFO_BYTES;
	wire	CRC_TO_FIFO_LAST;
	wire	CRC_TO_FIFO_ABORT;

	wire	msb_bytes;
	// }}}

	assign msb_bytes = (S_AXIN_BYTES == 2'b00) ? 1'b1 : 1'b0;
	assign M_AXIN_BYTES = M_BYTES[2:0];

	axinwidth #(
		// {{{
		.IW(32),    // Incoming data path width
		.OW(64)	    // Outgoing data path width
		// }}}
	) width (
		// {{{
		.ACLK(S_AXI_ACLK), 
		.ARESETN(S_AXI_ARESETN),
		// S_AXIN_*
		.S_AXIN_VALID(S_AXIN_VALID),
		.S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA(S_AXIN_DATA),
		.S_AXIN_BYTES({ msb_bytes, S_AXIN_BYTES }),
		.S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		// M_AXIN_*
		.M_AXIN_VALID(WIDTH_TO_CRC_VALID),
		.M_AXIN_READY(WIDTH_TO_CRC_READY),
		.M_AXIN_DATA(WIDTH_TO_CRC_DATA),
		.M_AXIN_BYTES(WIDTH_TO_CRC_BYTES),
		.M_AXIN_LAST(WIDTH_TO_CRC_LAST),
		.M_AXIN_ABORT(WIDTH_TO_CRC_ABORT)
		// }}}
	);

	crc_axin #(
		// {{{
		.DATA_WIDTH(64),
		.OPT_SKIDBUFFER(0),
		.OPT_LOWPOWER(0),
		.OPT_LITTLE_ENDIAN(1)
		// }}}
	) crc (
		// {{{
		// clk and low reset
		.ACLK(S_AXI_ACLK), 
		.ARESETN(S_AXI_ARESETN),
		// calculate crc if enable
		.i_cfg_en(1'b1),
		// S_AXIN_*: Incoming data
		.S_AXIN_VALID(WIDTH_TO_CRC_VALID),
		.S_AXIN_READY(WIDTH_TO_CRC_READY),
		.S_AXIN_DATA(WIDTH_TO_CRC_DATA),
		.S_AXIN_BYTES(WIDTH_TO_CRC_BYTES),
		.S_AXIN_LAST(WIDTH_TO_CRC_LAST),
		.S_AXIN_ABORT(WIDTH_TO_CRC_ABORT),
		// M_AXIN_*: Outgoing data
		.M_AXIN_VALID(M_AXIN_VALID),
		.M_AXIN_READY(M_AXIN_READY),
		.M_AXIN_DATA(M_AXIN_DATA),
		.M_AXIN_BYTES(M_BYTES),
		.M_AXIN_LAST(M_AXIN_LAST),
		.M_AXIN_ABORT(M_AXIN_ABORT)
		// }}}
	);

endmodule
