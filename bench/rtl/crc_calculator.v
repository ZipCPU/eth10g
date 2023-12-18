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
