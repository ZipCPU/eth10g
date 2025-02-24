////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/netdbggen.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
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
`timescale 1ns/1ps
`default_nettype none
// }}}
module	netdbggen (
		// {{{
		input	wire		i_clk, i_reset,	// @ 66b speed or faster
		//
		input	wire		i_phy_fault,
		input	wire		i_remote_fault, i_local_fault,
		// Raw incoming data stream
		//  {{{
		// No backpressure allowed here
		input	wire		i_p66b_valid,
		input	wire	[65:0]	i_p66b_data,
		// }}}
		// Packet completion notifications ...
		// {{{
		input	wire		i_rx_packet,
		input	wire	[17:0]	i_rx_pktlen,
		//
		input	wire		i_crc_packet,
		input	wire	[17:0]	i_crc_pktlen,
		//
		input	wire		i_txgate_packet,
		input	wire	[17:0]	i_txgate_pktlen,
		//
		input	wire		i_tx_packet,
		input	wire	[17:0]	i_tx_pktlen,
		// }}}
		// Outgoing AXI stream debugging port
		// {{{
		output	reg		o_dbg_valid,
		input	wire		i_dbg_ready,
		output	reg	[30:0]	o_dbg_data
		// }}}
		// }}}
	);

	localparam	[1:0]	SYNC_CONTROL = 2'b01, SYNC_DATA = 2'b10;
	localparam [6:0]	IDL = 7'h0;
	localparam [65:0]	P_IDLE = { {(8){IDL}}, 8'h1e, SYNC_CONTROL };

	////////////////////////////////////////////////////////////////////////
	//
	// Counter for async time handling
	// {{{
	reg		idle_en;
	reg	[7:0]	r_count;

	initial	{ idle_en, r_count } = 0;
	always @(posedge i_clk)
	if (i_reset)
		{ idle_en, r_count } <= 0;
	else if (i_p66b_valid)
		{ idle_en, r_count } <= r_count + 1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Shared status bits
	// {{{
	reg	[1:0]	lock_status;
	reg		r_phy_fault;
	reg	[1:0]	phy_fault_pipe;

	initial { r_phy_fault, phy_fault_pipe } = -1;
	always @(posedge i_clk)
		{ r_phy_fault, phy_fault_pipe } <= { phy_fault_pipe, i_phy_fault };

	always @(*)
	begin
		if (r_phy_fault)
			lock_status = 2'b11;
		else if (i_remote_fault)
			lock_status = 2'b10;
		else if (i_local_fault)
			lock_status = 2'b01;
		else
			lock_status = 2'b00;
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #0: IDLE
	// {{{
	localparam	LGIDLE = 12;

	reg	[LGIDLE:0]	idl_count;
	reg			idl_valid;
	reg			idl_ready;
	reg	[30:0]		idl_data;

	always @(posedge i_clk)
	if (i_reset)
		idl_count <= 0;
	else if (i_p66b_valid && lock_status == 2'b00 && i_p66b_data != P_IDLE)
		idl_count <= 0;
	else if (i_p66b_valid && !idl_count[LGIDLE])
		idl_count <= idl_count + 1;

	always @(posedge i_clk)
	if (i_reset)
		idl_valid <= 0;
	else if (idle_en && !r_phy_fault && idl_count[LGIDLE])
		idl_valid <= 1'b1;
	else if (idl_ready)
		idl_valid <= 1'b0;

	always @(posedge i_clk)
	if (!idl_valid || idl_ready)
		idl_data <= { 2'b00, 3'b0, 8'h0, 16'h0, SYNC_CONTROL };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #1: Control channel
	// {{{
	localparam	LGCTRL = 4;

	reg			pre_ctrl_valid, next_pre_ctrl_valid;
	wire			pre_ctrl_ready;
	reg	[2+8+66-1:0]	pre_ctrl_data;
	reg	[67:0]		pre_ctrl_last_word;

	wire	[LGCTRL:0]	ctrl_fifo_fill;
	wire			ctrl_fifo_full, ctrl_fifo_empty;

	reg			ctrl_valid, ctrl_last;
	reg			ctrl_ready;
	wire	[2+8+66-1:0]	ctrl_fifo_data;
	reg	[2+8+66-1:0]	ctrl_wide_data;
	reg	[1:0]		ctrl_dcount;

	wire	[30:0]		ctrl_data;

	// next_pre_ctrl_valid
	// {{{
	always @(*)
	begin
		next_pre_ctrl_valid = 1'b1;
		if (lock_status == 2'b00 &&( i_p66b_data[1:0] != SYNC_CONTROL
				|| pre_ctrl_last_word[1:0] != SYNC_CONTROL))
			next_pre_ctrl_valid = 1'b0;

		if ({ lock_status, i_p66b_data } == pre_ctrl_last_word)
			next_pre_ctrl_valid = 1'b0;
		if (!i_p66b_valid && lock_status == pre_ctrl_last_word[66 +: 2])
			next_pre_ctrl_valid = 1'b0;
	end
	// }}}

	initial	pre_ctrl_last_word = { 2'b11, 64'h0, 2'b11 };
	always @(posedge i_clk)
	if (i_p66b_valid)
		pre_ctrl_last_word <= { lock_status, i_p66b_data };
	else if (lock_status != pre_ctrl_last_word[66 +: 2])
	begin
		pre_ctrl_last_word[67:66] <= lock_status;
		pre_ctrl_last_word[1:0] <= 2'b11;
	end

	// pre_ctrl_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		pre_ctrl_valid <= 0;
	else if (next_pre_ctrl_valid)
		pre_ctrl_valid <= 1'b1;
	else if (pre_ctrl_ready)
		pre_ctrl_valid <= 1'b0;
	// }}}

	// pre_ctrl_data
	// {{{
	always @(posedge i_clk)
	if ((!pre_ctrl_valid || pre_ctrl_ready) && next_pre_ctrl_valid)
		pre_ctrl_data <= { lock_status, r_count, i_p66b_data };
	else if (pre_ctrl_valid && next_pre_ctrl_valid)
		pre_ctrl_data[1] <= 1'b1;
	// }}}

	// SFIFO -- to make sure we can ride through any sudden changes
	// {{{
	sfifo #(
		.BW(2+8+66), .LGFLEN(LGCTRL)
	) u_ctrl_fifo (
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wr(pre_ctrl_valid),
		.i_data(pre_ctrl_data), .o_full(ctrl_fifo_full),
			.o_fill(ctrl_fifo_fill),
		.i_rd(!ctrl_valid || (ctrl_ready && ctrl_last)),
			.o_data(ctrl_fifo_data), .o_empty(ctrl_fifo_empty)
	);

	assign	pre_ctrl_ready = !ctrl_fifo_full;
	// }}}

	// ctrl_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		ctrl_valid <= 1'b0;
	else if (!ctrl_valid || (ctrl_ready && ctrl_last))
		ctrl_valid <= !ctrl_fifo_empty;
	else if (ctrl_ready && ctrl_last)
		ctrl_valid <= 1'b0;
	// }}}

	// ctrl_wide_data
	// {{{
	always @(posedge i_clk)
	if (!ctrl_valid || (ctrl_ready && ctrl_last))
		ctrl_wide_data <= ctrl_fifo_data;
	else if (ctrl_ready)
		ctrl_wide_data <= { ctrl_wide_data[66 +: 2+8], 16'h0,
				ctrl_wide_data[2+16 +: 48],
					ctrl_wide_data[1:0] };
	// }}}

	assign	ctrl_data = { ctrl_wide_data[66+8 +: 2], 3'b001,
				ctrl_wide_data[66 +: 8],
				ctrl_wide_data[0 +: 16+2] };

	// ctrl_last, ctrl_dcount
	// {{{
	initial	ctrl_last = 1'b1;
	initial	ctrl_dcount = 2'b11;
	always @(posedge i_clk)
	if (i_reset)
	begin
		ctrl_last <= 1'b1;
		ctrl_dcount <= 2'b11;
	end else if (!ctrl_valid)
	begin
		ctrl_dcount <= 2'b11;
		ctrl_last <= ctrl_fifo_empty;
	end else if (ctrl_valid && ctrl_ready)
	begin
		ctrl_dcount <= ctrl_dcount - 1;
		ctrl_last <= (ctrl_dcount <= 2'b01);
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #2: Start of packets
	// {{{

	localparam	LGSTART = 3;

	wire			start_reset;
	reg			start_primed, start_triggered, start_halted;
	reg	[LGSTART-1:0]	start_halt_count;
	reg	[LGSTART-1:0]	start_waddr, start_raddr, start_prime_count;
	reg	[2+8+66-1:0]	start_mem	[0:((1<<LGSTART)-1)];
	reg	[2+8+66-1:0]	start_wide_data;

	reg			start_valid, start_last, start_eow;
	reg			start_ready;
	reg	[1:0]		start_sub;
	reg	[2:0]		start_count;

	wire	[30:0]		start_data;

	assign	start_reset = start_triggered && !start_valid && start_last
			&& i_p66b_valid && i_p66b_data[1:0] == SYNC_CONTROL;

	// start_primed, start_prime_count
	// {{{
	always @(posedge i_clk)
	if (i_reset || start_reset)
		{ start_primed, start_prime_count } <= 0;
	else if (i_p66b_valid && !start_primed)
		{ start_primed, start_prime_count } <= start_prime_count + 1;
	// }}}

	// start_triggered
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		start_triggered <= 0;
	else if (!start_triggered)
	begin
		if (r_phy_fault || i_remote_fault || i_local_fault)
			start_triggered <= 1'b0;
		else if (!start_primed)
			start_triggered <= 1'b0;
		else if (i_p66b_valid && i_p66b_data[1:0] == SYNC_DATA
				&& pre_ctrl_last_word[1:0] == SYNC_CONTROL)
			start_triggered <= 1'b1;
	end else if (start_reset)
		start_triggered <= 1'b0;
	// }}}

	// start_halted
	// {{{
	always @(posedge i_clk)
	if (i_reset || !start_triggered || !start_primed || start_reset)
	begin
		start_halt_count <= -2;
		start_halted <= 1'b0;
	end else if (i_p66b_valid && !start_halted)
		{ start_halted, start_halt_count } <= start_halt_count + 1;
	// }}}

	// start_waddr
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		start_waddr <= 0;
	else if (!start_halted && i_p66b_valid)
		start_waddr <= start_waddr + 1;
	// }}}

	always @(posedge i_clk)
	if (!start_halted && i_p66b_valid)
		start_mem[start_waddr] <= { lock_status,r_count, i_p66b_data };

	// start_raddr
	// {{{
	always @(posedge i_clk)
	if (!start_halted)
		start_raddr <= start_waddr + (i_p66b_valid ? 1:0) - 4;
	else if (!start_valid || (start_ready && start_eow))
		start_raddr <= start_raddr + 1;
	// }}}

	// start_wide_data
	// {{{
	always @(posedge i_clk)
	if (!start_valid || (start_ready && start_eow))
		start_wide_data <= start_mem[start_raddr];
	else if (start_valid && start_ready)
		start_wide_data <= { start_wide_data[66 +: 2+8], 16'h0,
					start_wide_data[16+2 +: 48],
					start_wide_data[1:0] };
	// }}}

	// start_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		start_valid <= 1'b0;
	else if (!start_valid && start_halted && !start_last)
		start_valid <= 1'b1;
	else if (start_valid && start_ready && start_last)
		start_valid <= 1'b0;
	// }}}

	// start_last, start_count, start_eow, start_sub
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		{ start_last, start_count, start_eow, start_sub } <= 0;
	else if (!start_triggered || start_reset)
		{ start_last, start_count, start_eow, start_sub } <= 0;
	else if (start_valid && start_ready)
	begin
		start_sub <= start_sub + 1;
		start_eow <= (start_sub == 2'b10);
		if (start_eow)
			start_count <= start_count + 1;

		if (start_last)
			start_last <= 1'b1;
		else if (start_sub != 2'b10)
			start_last <= 1'b0;
		else if (start_count >= 3)
			start_last <= 1'b1;
	end
	// }}}

	assign	start_data = { start_wide_data[66+8 +: 2], 3'b010,
			start_wide_data[66 +: 8], start_wide_data[0 +: 2+16] };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #3: End of packets
	// {{{

	localparam	LGEOP = 3;

	wire			eop_reset;
	reg			eop_primed, eop_triggered, eop_halted;
	reg	[LGEOP-1:0]	eop_halt_count;
	reg	[LGEOP-1:0]	eop_waddr, eop_raddr, eop_prime_count;
	reg	[2+8+66-1:0]	eop_mem	[0:((1<<LGEOP)-1)];
	reg	[2+8+66-1:0]	eop_wide_data;

	reg			eop_valid, eop_last, eop_eow;
	reg			eop_ready;
	reg	[1:0]		eop_sub;
	reg	[2:0]		eop_count;

	wire	[30:0]		eop_data;

	assign	eop_reset = eop_triggered && !eop_valid && eop_last
			&& i_p66b_valid && i_p66b_data[1:0] == SYNC_CONTROL;

	// eop_primed, eop_prime_count
	// {{{
	always @(posedge i_clk)
	if (i_reset || eop_reset)
		{ eop_primed, eop_prime_count } <= 0;
	else if (i_p66b_valid && !eop_primed)
		{ eop_primed, eop_prime_count } <= eop_prime_count + 1;
	// }}}

	// eop_triggered
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		eop_triggered <= 0;
	else if (!eop_triggered)
	begin
		if (r_phy_fault || i_remote_fault || i_local_fault)
			eop_triggered <= 1'b0;
		else if (!eop_primed)
			eop_triggered <= 1'b0;
		else if (i_p66b_valid && i_p66b_data[1:0] == SYNC_CONTROL
				&& pre_ctrl_last_word[1:0] == SYNC_DATA)
			eop_triggered <= 1'b1;
	end else if (eop_reset)
		eop_triggered <= 1'b0;
	// }}}

	// eop_halted
	// {{{
	always @(posedge i_clk)
	if (i_reset || !eop_triggered || !eop_primed || eop_reset)
	begin
		eop_halt_count <= -1;
		eop_halted <= 1'b0;
	end else if (i_p66b_valid && !eop_halted)
		{ eop_halted, eop_halt_count } <= eop_halt_count + 1;
	// }}}

	// eop_waddr
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		eop_waddr <= 0;
	else if (!eop_halted && i_p66b_valid)
		eop_waddr <= eop_waddr + 1;
	// }}}

	always @(posedge i_clk)
	if (!eop_halted && i_p66b_valid)
		eop_mem[eop_waddr] <= { lock_status,r_count, i_p66b_data };

	// eop_raddr
	// {{{
	always @(posedge i_clk)
	if (!eop_halted)
		eop_raddr <= eop_waddr + (i_p66b_valid ? 1:0) - 4;
	else if (!eop_valid || (eop_ready && eop_eow))
		eop_raddr <= eop_raddr + 1;
	// }}}

	// eop_wide_data
	// {{{
	always @(posedge i_clk)
	if (!eop_valid || (eop_ready && eop_eow))
		eop_wide_data <= eop_mem[eop_raddr];
	else if (eop_valid && eop_ready)
		eop_wide_data <= { eop_wide_data[66 +: 2+8], 16'h0,
					eop_wide_data[16+2 +: 48],
					eop_wide_data[1:0] };
	// }}}

	// eop_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		eop_valid <= 1'b0;
	else if (!eop_valid && eop_halted && !eop_last)
		eop_valid <= 1'b1;
	else if (eop_valid && eop_ready && eop_last)
		eop_valid <= 1'b0;
	// }}}

	// eop_last, eop_count, eop_eow, eop_sub
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		{ eop_last, eop_count, eop_eow, eop_sub } <= 0;
	else if (!eop_triggered || eop_reset)
		{ eop_last, eop_count, eop_eow, eop_sub } <= 0;
	else if (eop_valid && eop_ready)
	begin
		eop_sub <= eop_sub + 1;
		eop_eow <= (eop_sub == 2'b10);
		if (eop_eow)
			eop_count <= eop_count + 1;

		if (eop_last)
			eop_last <= 1'b1;
		else if (eop_sub != 2'b10)
			eop_last <= 1'b0;
		else if (eop_count >= 3)
			eop_last <= 1'b1;
	end
	// }}}

	assign	eop_data = { eop_wide_data[66+8 +: 2], 3'b011,
			eop_wide_data[66 +: 8], eop_wide_data[0 +: 2+16] };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #4: RX packets
	// {{{

	reg		stat_rx_valid;
	reg		stat_rx_ready;
	reg	[27:0]	stat_rx_raw_data;
	wire	[30:0]	stat_rx_data;

	always @(posedge i_clk)
	if (i_reset)
		stat_rx_valid <= 1'b0;
	else if (i_rx_packet)
		stat_rx_valid <= 1'b1;
	else if (stat_rx_ready)
		stat_rx_valid <= 1'b0;

	always @(posedge i_clk)
	if ((!stat_rx_valid || stat_rx_ready) && i_rx_packet)
	begin
		stat_rx_raw_data <= { lock_status, r_count[7:2], i_rx_pktlen, 2'b00 };
		if (i_p66b_valid)
			stat_rx_raw_data[1:0] <= i_p66b_data[1:0];
		else
			stat_rx_raw_data[1:0] <= pre_ctrl_last_word[1:0];
	end

	assign	stat_rx_data = { stat_rx_raw_data[2+16+8 +: 2], 3'b100,
			stat_rx_raw_data[0 +: 2 + 16 + 8] };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #5: RX CRC Packets
	// {{{

	reg		stat_crc_valid;
	reg		stat_crc_ready;
	reg	[27:0]	stat_crc_raw_data;
	wire	[30:0]	stat_crc_data;

	always @(posedge i_clk)
	if (i_reset)
		stat_crc_valid <= 1'b0;
	else if (i_crc_packet)
		stat_crc_valid <= 1'b1;
	else if (stat_crc_ready)
		stat_crc_valid <= 1'b0;

	always @(posedge i_clk)
	if ((!stat_crc_valid || stat_crc_ready) && i_crc_packet)
	begin
		stat_crc_raw_data <= { lock_status, r_count[7:2], i_crc_pktlen,
								2'b00 };
		if (i_p66b_valid)
			stat_crc_raw_data[1:0] <= i_p66b_data[1:0];
		else
			stat_crc_raw_data[1:0] <= pre_ctrl_last_word[1:0];
	end

	assign	stat_crc_data = { stat_crc_raw_data[2+16+8 +: 2], 3'b101,
			stat_crc_raw_data[0 +: 2 + 16 + 8] };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #6: TX Packets
	// {{{

	reg		stat_tx_valid;
	reg		stat_tx_ready;
	reg	[27:0]	stat_tx_raw_data;
	wire	[30:0]	stat_tx_data;


	always @(posedge i_clk)
	if (i_reset)
		stat_tx_valid <= 1'b0;
	else if (i_tx_packet)
		stat_tx_valid <= 1'b1;
	else if (stat_tx_ready)
		stat_tx_valid <= 1'b0;

	always @(posedge i_clk)
	if ((!stat_tx_valid || stat_tx_ready) && i_tx_packet)
	begin
		stat_tx_raw_data <= { lock_status, r_count[7:2], i_tx_pktlen,
								2'b00 };
		if (i_p66b_valid)
			stat_tx_raw_data[1:0] <= i_p66b_data[1:0];
		else
			stat_tx_raw_data[1:0] <= pre_ctrl_last_word[1:0];
	end

	assign	stat_tx_data = { stat_tx_raw_data[2+16+8 +: 2], 3'b110,
			stat_tx_raw_data[0 +: 2 + 16 + 8] };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #7: TX Gate packets
	// {{{

	reg		stat_txgate_valid;
	reg		stat_txgate_ready;
	reg	[27:0]	stat_txgate_raw_data;
	wire	[30:0]	stat_txgate_data;


	always @(posedge i_clk)
	if (i_reset)
		stat_txgate_valid <= 1'b0;
	else if (i_txgate_packet)
		stat_txgate_valid <= 1'b1;
	else if (stat_txgate_ready)
		stat_txgate_valid <= 1'b0;

	always @(posedge i_clk)
	if ((!stat_txgate_valid || stat_txgate_ready) && i_txgate_packet)
	begin
		stat_txgate_raw_data <= { lock_status, r_count[7:2], i_txgate_pktlen,
								2'b00 };
		if (i_p66b_valid)
			stat_txgate_raw_data[1:0] <= i_p66b_data[1:0];
		else
			stat_txgate_raw_data[1:0] <= pre_ctrl_last_word[1:0];
	end

	assign	stat_txgate_data = { stat_txgate_raw_data[2+16+8 +: 2], 3'b111,
			stat_txgate_raw_data[0 +: 2+16+8] };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Arbiter
	// {{{

	wire	[7:0]	request_vec, w_grant;
	reg	[30:0]	pre_exfifo_data;

	always @(*)
	if (o_dbg_valid && !i_dbg_ready)
	begin
		{ stat_txgate_ready, stat_tx_ready, stat_crc_ready,
			  stat_rx_ready, eop_ready, start_ready,
			  ctrl_ready, idl_ready } = 8'h0;
	end else begin
		{ stat_txgate_ready, stat_tx_ready, stat_crc_ready,
			  stat_rx_ready, eop_ready, start_ready,
			  ctrl_ready, idl_ready } = w_grant;
	end

	assign	request_vec = { stat_txgate_valid, stat_tx_valid,
			stat_crc_valid, stat_rx_valid, eop_valid, start_valid,
			ctrl_valid, idl_valid };
	pktarbiter #(
		.W(8)
	) u_arbiter (
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.i_req(request_vec),
		.i_stall(|(w_grant & request_vec)),
		.o_grant(w_grant)
	);

	always @(posedge i_clk)
	if (i_reset)
		o_dbg_valid <= 1'b0;
	else if (!o_dbg_valid || i_dbg_ready)
		o_dbg_valid <= |(w_grant & request_vec);

	always @(*)
	begin
		pre_exfifo_data = 31'h0;
		if (w_grant[7])
			pre_exfifo_data = pre_exfifo_data | stat_txgate_data;
		if (w_grant[6])
			pre_exfifo_data = pre_exfifo_data | stat_tx_data;
		if (w_grant[5])
			pre_exfifo_data = pre_exfifo_data | stat_crc_data;
		if (w_grant[4])
			pre_exfifo_data = pre_exfifo_data | stat_rx_data;
		if (w_grant[3])
			pre_exfifo_data = pre_exfifo_data | eop_data;
		if (w_grant[2])
			pre_exfifo_data = pre_exfifo_data | start_data;
		if (w_grant[1])
			pre_exfifo_data = pre_exfifo_data | ctrl_data;
		if (w_grant[0])
			pre_exfifo_data = pre_exfifo_data | idl_data;
	end

	always @(posedge i_clk)
	if (i_reset)
		o_dbg_data <= 31'h0;
	else if (!o_dbg_valid || i_dbg_ready)
		o_dbg_data <= pre_exfifo_data;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ctrl_fifo_fill };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
