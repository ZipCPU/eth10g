////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	scoreboard.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Compares two AXI packet streams, to determine if the packets
//		generated in either stream match.  The idea is that, if the
//	test works, the packets should match.  If not, the packets won't match,
//	and the test will fail.
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
`timescale 1 ns/1 ps
// }}}
module scoreboard (
		// {{{
		// clk, reset
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		// model channel
		input	wire		MODEL_AXIN_VALID,
		output	wire		MODEL_AXIN_READY,
		input	wire	[2:0]	MODEL_AXIN_BYTES,
		input	wire	[63:0]	MODEL_AXIN_DATA,
		input	wire		MODEL_AXIN_LAST,
		input	wire		MODEL_AXIN_ABORT,
		// crc_calculator channel
		input	wire		CRC_AXIN_VALID,
		output	wire		CRC_AXIN_READY,
		input	wire	[2:0]	CRC_AXIN_BYTES,
		input	wire	[63:0]	CRC_AXIN_DATA,
		input	wire		CRC_AXIN_LAST,
		input	wire		CRC_AXIN_ABORT,
		//
		output	reg		is_passed,
		output	reg	[5:0]	crc_packets_rcvd,
		output	reg	[5:0]	model_packets_rcvd
		// }}}
	);

	// Local declarations
	// {{{
	wire		CRC_FIFO_VALID;
	reg	CRC_FIFO_READY;
	wire	[63:0]	CRC_FIFO_DATA;
	wire	[2:0]	CRC_FIFO_BYTES;
	wire		CRC_FIFO_LAST;
	wire		CRC_FIFO_ABORT;

	reg	[2:0]	last_bytes;
	reg	[10:0]	model_stream_word;
	// crc_calculator word and packet count
	reg	[10:0]	crc_stream_word;

	// check if data are matched or not
	reg	is_first_data;
	// }}}

	// Instantiate the FIFO
	netfifo #(
		// {{{
		.BW(64),
		.LGFLEN(6),
		.OPT_ASYNC_READ(1'b1),
		.OPT_WRITE_ON_FULL(1'b1),
		.OPT_READ_ON_EMPTY(1'b0)
		// }}}
	) u_fifo (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIN_VALID(CRC_AXIN_VALID),
		.S_AXIN_READY(CRC_AXIN_READY),
		.S_AXIN_DATA(CRC_AXIN_DATA),
		.S_AXIN_LAST(CRC_AXIN_LAST),
		.S_AXIN_ABORT(CRC_AXIN_ABORT),
		//
		.M_AXIN_VALID(CRC_FIFO_VALID),
		.M_AXIN_READY(CRC_FIFO_READY),
		.M_AXIN_DATA(CRC_FIFO_DATA),
		.M_AXIN_LAST(CRC_FIFO_LAST),
		.M_AXIN_ABORT(CRC_FIFO_ABORT)
		// }}}
	);

	// BYTES
	assign CRC_FIFO_BYTES = CRC_FIFO_LAST ? last_bytes : 3'b000;

	// last_bytes
	// {{{
	initial last_bytes = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || is_first_data)
		last_bytes <= 0;
	else if (CRC_AXIN_VALID && CRC_AXIN_READY && CRC_AXIN_LAST)
		last_bytes <= CRC_AXIN_BYTES;
	// }}}

	// model word and packet count
	assign MODEL_AXIN_READY = 1'b1;

	// model_stream_word
	// {{{
	initial CRC_FIFO_READY = 0;
	initial	model_stream_word = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		CRC_FIFO_READY <= 0;
		model_stream_word <= 0;
	end else if (MODEL_AXIN_VALID && MODEL_AXIN_READY)
	begin
		CRC_FIFO_READY <= 1;
		model_stream_word <= model_stream_word + 1;
		if (MODEL_AXIN_LAST)
			model_stream_word <= 0;
	end else
		CRC_FIFO_READY <= 0;
	// }}}

	initial	model_packets_rcvd = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		model_packets_rcvd <= 0;
	else if (MODEL_AXIN_VALID && MODEL_AXIN_READY && MODEL_AXIN_LAST)
		model_packets_rcvd <= model_packets_rcvd + 1;

	// assign CRC_AXIN_READY = 1'b1;

	initial	crc_stream_word = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		crc_stream_word <= 0;
	else if (CRC_FIFO_VALID && CRC_FIFO_READY)
	begin
		crc_stream_word <= crc_stream_word + 1;
		if (CRC_FIFO_LAST)
			crc_stream_word <= 0;
	end

	initial	crc_packets_rcvd = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		crc_packets_rcvd <= 0;
	else if (CRC_AXIN_VALID && CRC_AXIN_READY && CRC_AXIN_LAST)
		crc_packets_rcvd <= crc_packets_rcvd + 1;

    
	initial is_first_data = 1;
	initial is_passed = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		is_first_data <= 1;
		is_passed <= 0;
	end else if (CRC_FIFO_VALID && MODEL_AXIN_VALID)
	begin
		if (CRC_FIFO_LAST && MODEL_AXIN_LAST)
		begin
			is_first_data <= 1;
			if (MODEL_AXIN_BYTES != CRC_FIFO_BYTES)
				$display("WARNING: Bytes values of last data aren't matched");
		end else
			is_first_data <= 0;

		if ((CRC_FIFO_DATA == MODEL_AXIN_DATA) && (is_first_data || is_passed))
			is_passed <= 1;
		else
			is_passed <= 0;
	end else
		is_passed <= !is_first_data;

endmodule
