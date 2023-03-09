////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/pktvfifo.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A virtual packet FIFO.  Fundamentally, this core acts as a
//		FIFO.  The memory used by it, however, is externally accessed
//	via a Wishbone bus.
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
// The WB2AXIP project contains free software and gateware, licensed under the
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
// Until we define the logic, local registers will not be used
// Verilator lint_off UNUSED
// Verilator lint_off UNDRIVEN
module	pktvfifo #(
		// {{{
		parameter	PKTDW = 64,
		parameter	PKTBYW = $clog2(PKTDW/8),
		parameter	BUSDW = 512,
		parameter	AW = 30-$clog2(BUSDW/8)
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// WB Control port
		// {{{
		input	wire		i_ctrl_cyc, i_ctrl_stb, i_ctrl_we,
		input	wire	[1:0]	i_ctrl_addr,
		input	wire	[31:0]	i_ctrl_data,
		input	wire	[3:0]	i_ctrl_sel,
		output	wire		o_ctrl_stall,
		output	wire		o_ctrl_ack,
		output	wire	[31:0]	o_ctrl_data,
		// }}}
		// Incoming packet
		// {{{
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[PKTDW-1:0]	S_DATA,
		input	wire	[PKTBYW-1:0]	S_BYTES,
		input	wire			S_LAST,
		input	wire			S_ABORT,
		// }}}
		// DMA bus interface
		// {{{
		output	wire			o_wb_cyc, o_wb_stb, o_wb_we,
		output	wire	[AW-1:0]	o_wb_addr,
		output	wire	[BUSDW-1:0]	o_wb_data,
		output	wire	[BUSDW/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall,
		input	wire			i_wb_ack,
		input	wire	[BUSDW-1:0]	i_wb_data,
		input	wire			i_wb_err,
		// }}}
		// Outgoing packet
		// {{{
		output	wire			M_VALID,
		input	wire			M_READY,
		output	wire	[PKTDW-1:0]	M_DATA,
		output	wire	[PKTBYW-1:0]	M_BYTES,
		output	wire			M_LAST,
		output	wire			M_ABORT
		// }}}
		// }}}
	);

endmodule
// Verilator lint_on  UNDRIVEN
// Verilator lint_on  UNUSED
