////////////////////////////////////////////////////////////////////////////////
//
// Filename:	bench/rtl/scoreboard.v
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
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
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
`timescale 1 ns/1 ps
`default_nettype none
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
		output	reg		is_passed, pkt_fail,
		output	reg	[5:0]	crc_packets_rcvd,
		output	reg	[5:0]	model_packets_rcvd
		// }}}
	);

	// Local declarations
	// {{{
	wire		CRC_FIFO_VALID;
	wire		CRC_FIFO_READY;
	wire	[63:0]	CRC_FIFO_DATA;
	wire	[2:0]	CRC_FIFO_BYTES;
	wire		CRC_FIFO_LAST;
	wire		CRC_FIFO_ABORT;

	reg	[10:0]	model_stream_word;
	// crc_calculator word and packet count
	reg	[10:0]	crc_stream_word;

	// check if data are matched or not
	reg	is_first_data;
	reg	beat_match;
	reg	[63:0]	match_mask;
	// }}}

	// Instantiate the FIFO
	netfifo #(
		// {{{
		.BW(64 + 3),
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
		.S_AXIN_DATA({ CRC_AXIN_BYTES, CRC_AXIN_DATA }),
		.S_AXIN_LAST(CRC_AXIN_LAST),
		.S_AXIN_ABORT(CRC_AXIN_ABORT),
		//
		.M_AXIN_VALID(CRC_FIFO_VALID),
		.M_AXIN_READY(CRC_FIFO_READY),
		.M_AXIN_DATA({ CRC_FIFO_BYTES, CRC_FIFO_DATA }),
		.M_AXIN_LAST(CRC_FIFO_LAST),
		.M_AXIN_ABORT(CRC_FIFO_ABORT)
		// }}}
	);

	// model word and packet count
	assign MODEL_AXIN_READY = 1'b1;

	// model_stream_word
	// {{{
    assign CRC_FIFO_READY = (MODEL_AXIN_VALID && MODEL_AXIN_READY) ? 1 : 0;
	initial	model_stream_word = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		model_stream_word <= 0;
	else if (MODEL_AXIN_VALID && MODEL_AXIN_READY)
	begin
		model_stream_word <= model_stream_word + 1;
		if (MODEL_AXIN_LAST)
			model_stream_word <= 0;
	end
	// }}}

	initial	model_packets_rcvd = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		model_packets_rcvd <= 0;
	else if (MODEL_AXIN_VALID && MODEL_AXIN_READY && MODEL_AXIN_LAST)
		model_packets_rcvd <= model_packets_rcvd + 1;

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
	else if (CRC_FIFO_VALID && CRC_FIFO_READY && CRC_FIFO_LAST)
		crc_packets_rcvd <= crc_packets_rcvd + 1;

	always @(*)
	begin
		if (CRC_FIFO_BYTES == 0)
			match_mask = -1;
		else
			match_mask = {(64){1'b1}} >> (8*(8-CRC_FIFO_BYTES));

		beat_match = (CRC_FIFO_VALID && MODEL_AXIN_VALID);
		if (CRC_FIFO_LAST != MODEL_AXIN_LAST)
			beat_match = 1'b0;
		if (MODEL_AXIN_BYTES != CRC_FIFO_BYTES)
			beat_match = 1'b0;
		if (0 != (match_mask & (CRC_FIFO_DATA ^ MODEL_AXIN_DATA)))
			beat_match = 1'b0;
	end

	initial is_first_data = 1;
	initial is_passed = 0;
	initial	pkt_fail  = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || CRC_FIFO_ABORT || MODEL_AXIN_ABORT)
	begin
		is_first_data <= 1;
		is_passed <= 0;
		pkt_fail  <= 0;
	end else if (CRC_FIFO_VALID && MODEL_AXIN_VALID)
	begin
		if (!beat_match)
			is_passed <= 1'b0;
		else if (is_first_data)
			is_passed <= 1'b1;

		pkt_fail <= !beat_match ||(!is_first_data && !is_passed);

		if (CRC_FIFO_LAST && MODEL_AXIN_LAST)
		begin
			is_first_data <= 1;
			if (MODEL_AXIN_BYTES != CRC_FIFO_BYTES)
			begin
				$display("WARNING: Byte count of last beat doesn\'t match.  %2d != %2d (DUT)", CRC_FIFO_BYTES, MODEL_AXIN_BYTES);
			end
		end else
			is_first_data <= 0;

	end else if (is_first_data && (!CRC_FIFO_VALID || !MODEL_AXIN_VALID))
	begin
		is_passed <= 1'b0;
		pkt_fail  <= 1'b0;
	end

endmodule
