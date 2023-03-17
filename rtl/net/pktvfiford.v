////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/pktvfiford.v
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
module	pktvfiford #(
		// {{{
		parameter	BUSDW = 512,
		parameter	AW = 30-$clog2(BUSDW/8),
		parameter	LGFIFO = 5,
		parameter	LGPIPE = 6,
		parameter [0:0]	OPT_LOWPOWER = 1,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 0
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// WB Control port
		// {{{
		input	wire			i_cfg_reset_fifo, i_cfg_mem_err,
		input	wire	[AW-1:0]	i_cfg_baseaddr,
		input	wire	[AW-1:0]	i_cfg_memsize,
		input	wire	[AW+WBLSB-3:0]	i_writeptr,
		output	wire	[AW+WBLSB-3:0]	o_readptr,
		output	reg			o_fifo_err,
		// }}}
		// DMA bus interface
		// {{{
		output	reg			o_wb_cyc, o_wb_stb,
		output	wire			o_wb_we,
		output	wire	[AW-1:0]	o_wb_addr,
		output	wire	[BUSDW-1:0]	o_wb_data,
		output	reg	[BUSDW/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall,
		//
		input	wire			i_wb_ack,
		input	wire	[BUSDW-1:0]	i_wb_data,
		input	wire			i_wb_err,
		// }}}
		// Outgoing packet
		// {{{
		output	reg			M_VALID,
		// input wire			M_READY, // No backpressure supt
		output	reg	[BUSDW-1:0]	M_DATA,
		output	reg [$clog2(BUSDW/8)-1:0] M_BYTES,
		output	reg			M_LAST,
		// output wire			M_ABORT, // No ABORT support
		input	wire			i_fifo_rd
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	// Local parameters
	// {{{
	localparam	WBLSB = $clog2(BUSDW/8);

	localparam	[1:0]	RD_IDLE      = 2'h0,
				RD_SIZE      = 2'h1,
				RD_PACKET    = 2'h2,
				RD_CLEARBUS  = 2'h3;
	// }}}

	reg	[AW+WBLSB-1:0]	wide_baseaddr, wide_memsize, // wide_writeptr
				wide_readptr, end_of_memory;

	reg	[AW+(WBLSB-2)-1:0]	r_readptr, rd_wb_addr;

	reg	[LGPIPE:0]	rd_outstanding;
	reg			lastack;

	reg	[LGFIFO:0]	fifo_space;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Control logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		wide_baseaddr = 0;
		wide_baseaddr = { i_cfg_baseaddr, {(WBLSB){1'b0}} };

		wide_memsize  = 0;
		wide_memsize  = { i_cfg_memsize, {(WBLSB){1'b0}} };

		// wide_writeptr = 0;
		// wide_writeptr = { i_writeptr, 2'b00 };

		wide_readptr  = 0;
		wide_readptr  = { r_readptr, 2'b00 };
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read packets back out from memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[AW+WBLSB-1:0]	rd_requested, rd_pktlen;
	reg	[31:0]		next_rdlen;
	reg	[1:0]		rd_state;
	reg	[BUSDW-1:0]	wide_next_rdlen;

	always @(*)
	begin
		wide_next_rdlen = i_wb_data >> (32*r_readptr[WBLSB-3:0]);
		next_rdlen = wide_next_rdlen[31:0];
	end

	// next_rdaddr
	// {{{
	// Full (octet) address width
	reg	[AW+WBLSB-1:0]	next_rdaddr;
	always @(*)
	begin
		if (rd_pktlen == 0)
			next_rdaddr = { r_readptr, 2'b00 } + 4;
		else if (rd_requested + (BUSDW/8) <= rd_pktlen)
			next_rdaddr = { r_readptr, 2'b00 } + BUSDW/8;
		else begin
			next_rdaddr = { r_readptr, 2'b00 }
				+ (rd_pktlen + 3 - rd_requested);
			next_rdaddr[1:0] = 2'b0;
		end

		if (next_rdaddr >= end_of_memory)
			next_rdaddr = next_rdaddr - { i_cfg_memsize, {(WBLSB){1'b0}} };
	end
	// }}}

	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err
						|| (o_wb_cyc && i_wb_err))
	begin
		// {{{
		o_wb_cyc  <= 0;
		o_wb_stb  <= 0;
		rd_wb_addr <= 0;
		// o_wb_data <= 0;
		o_wb_sel  <= 0;
		r_readptr <= { i_cfg_baseaddr, {(WBLSB-2){1'b0}} };
		rd_state  <= RD_IDLE;
		rd_pktlen <= 0;
		// }}}
	end else case(rd_state)
	RD_IDLE: begin
		// {{{
		o_wb_cyc  <= 1'b0;
		o_wb_stb  <= 1'b0;
		rd_wb_addr <= r_readptr;
		rd_requested <= 0;
		rd_pktlen  <= 0;

		if (i_writeptr != r_readptr)
		begin
			// Issue a read command to capture the packet length
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			if (OPT_LITTLE_ENDIAN)
				o_wb_sel <= { {(BUSDW/8-4){1'b0}}, 4'hf }
						<< (4*r_readptr[WBLSB-3:0]);
			else
				o_wb_sel <= { 4'hf, {(BUSDW/8-4){1'b0}} }
						>> (4*r_readptr[WBLSB-3:0]);
			rd_state <= RD_SIZE;
		end end
		// }}}
	RD_SIZE: begin
		// {{{
		rd_requested <= 0;
		rd_pktlen  <= 0;

		if (!i_wb_stall)
			o_wb_stb <= 1'b0;
		if (i_wb_ack)
		begin
			o_wb_cyc <= 1'b0;
			rd_pktlen <= next_rdlen[AW+WBLSB-1:0];
			if (next_rdlen > 0)
			begin
				rd_state <= RD_PACKET;
				rd_wb_addr <= next_rdaddr[AW+WBLSB-1:2];
			end else
				rd_state <= RD_IDLE;
		end end
		// }}}
	RD_PACKET: begin
		// {{{
		if (!o_wb_stb || !i_wb_stall)
		begin
			if (lastack)
				o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
			o_wb_sel <= {(BUSDW/8){1'b1}};
			if ((rd_requested + (o_wb_stb ? (1<<WBLSB) : 0)
					< rd_pktlen)//+wide_readptr[WBLSB-1:2])
					&& !rd_outstanding[LGPIPE]
					&& (fifo_space > (o_wb_stb ? 1:0)))
				{ o_wb_cyc, o_wb_stb } <= 2'b11;

			if (o_wb_stb)
			begin
				rd_wb_addr <= next_rdaddr[AW+WBLSB-1:2];
				rd_requested <= rd_requested + (1<<WBLSB);
			end

			if (rd_requested >= rd_pktlen)
				rd_state <= RD_CLEARBUS;
		end end
		// }}}
	RD_CLEARBUS: begin
		// {{{
		if (!i_wb_stall)
			o_wb_stb <= 1'b0;
		if (!o_wb_stb && rd_outstanding == (i_wb_ack ? 1:0))
		begin
			o_wb_cyc <= 1'b0;
			// r_readptr <= next_readptr;
			rd_state <= RD_IDLE;
		end end
		// }}}
	default: begin end
	endcase

	// rd_outstanding
	// {{{
	initial	rd_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err)
		rd_outstanding <= 0;
	else case ({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b10: rd_outstanding <= rd_outstanding + 1;
	2'b01: rd_outstanding <= rd_outstanding - 1;
	default: begin end
	endcase
	// }}}

	// fifo_space
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err)
		fifo_space <= 1<<LGFIFO;
	else case({ i_wb_ack, i_fifo_rd })
	2'b10: fifo_space <= fifo_space - 1;
	2'b01: fifo_space <= fifo_space + 1;
	default: begin end
	endcase
	// }}}

	assign	o_wb_we   = 1'b0;
	assign	o_wb_data = {(BUSDW){1'b0}};
	assign	o_wb_sel  = -1;
	assign	o_wb_addr = rd_wb_addr[AW+(WBLSB-2)-1:(WBLSB-2)];

	assign	o_readptr = r_readptr;

	always @(*)
	begin
		lastack = (rd_outstanding + ((o_wb_stb && !i_wb_stall) ? 1:0)
					== (i_wb_ack ? 1:0));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory size handling/checking, fifo error generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg			dly_check, dly_fifo_err;
	reg	[AW+WBLSB-1:0]	mem_fill;

	// o_fifo_err
	// {{{
	//	Two causes of FIFO errors:
	//	1. A zero length, after we've been told there's something there
	//	2. A packet that passes the write pointer
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		o_fifo_err <= 1'b0;
	else if (dly_fifo_err)
		o_fifo_err <= 1'b1;
	else if (i_wb_ack && rd_state == RD_SIZE
			&& (next_rdlen[AW+WBLSB-1:0] == 0)
				|| (next_rdlen[31:AW+WBLSB] != 0))
		o_fifo_err <= 1'b1;
	else
		o_fifo_err <= 1'b0;
	// }}}

	// dly_check
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		dly_check <= 1'b0;
	else if (i_wb_ack && rd_state == RD_SIZE)
	begin
		dly_check <= 1'b1;
	end else
		dly_check <= 1'b0;
	// }}}

	// mem_fill
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		mem_fill <= 0;
	else if (i_writeptr < r_readptr)
		mem_fill <= { i_writeptr, 2'b00 } - { r_readptr, 2'b00 }
							+ wide_memsize;
	else
		mem_fill <= { i_writeptr, 2'b00 } - { r_readptr, 2'b00 };
	// }}}

	// dly_fifo_err
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || !dly_check)
		dly_fifo_err <= 1'b0;
	else
		dly_fifo_err <= (mem_fill < rd_pktlen + 4);
	// }}}

	always @(posedge i_clk)
		end_of_memory <= wide_baseaddr + wide_memsize;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Realign data, push return results out
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg			full_return, false_ack, pre_false_ack;
	reg	[AW+WBLSB-1:0]	return_len, next_return_len;
	reg	[BUSDW-1:0]	sreg;

	// full_return: Should an ACK trigger a full DW/8 output?
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE
							|| rd_state == RD_SIZE)
		full_return <= r_readptr[WBLSB-3:0] == 0;
	else if (i_wb_ack)
		full_return <= 1'b1;
	// }}}

	// M_VALID
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		M_VALID <= 1'b0;
	else if ((i_wb_ack && full_return) || false_ack)
		M_VALID <= 1'b1;
	else
		M_VALID <= 1'b0;
	// }}}

	// return_len: How many more bytes are to be expected?
	// {{{
	always @(*)
	begin
		// if (!full_return)
		//	next_return_len = (1<<WBLSB)-r_readptr[WBLSB-3:0],2'b0
		if (return_len >= BUSDW/8)
			next_return_len = return_len - BUSDW/8;
		else
			next_return_len = 0;
	end

	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE)
		return_len <= 0;
	else if (i_wb_ack && rd_state == RD_SIZE)
		return_len <= next_rdlen[AW+WBLSB-1:0];
	else if ((i_wb_ack && full_return) || false_ack)
	begin
		return_len <= next_return_len;
	end
	// }}}

	// false_ack: When do we clear our shift register?
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		{ false_ack, pre_false_ack } <= 0;
	else if (rd_state != RD_CLEARBUS)
		{ false_ack, pre_false_ack } <= { pre_false_ack, 1'b0 };
	else if (!o_wb_stb && rd_outstanding == (i_wb_ack ? 1:0)
				&& return_len[WBLSB-1:0] != 0)
		{ false_ack, pre_false_ack } <= (i_wb_ack) ? 2'b01 : 2'b10;
	// }}}

	// M_BYTE
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_SIZE)
		M_BYTES <= 0;
	else if (return_len >= (1<<WBLSB))
		M_BYTES <= 0;
	else
		M_BYTES <= return_len[WBLSB-1:0];
	// }}}

	// M_DATA (and sreg)
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE
							|| rd_state == RD_SIZE)
		{ M_DATA, sreg } <= 0;
	else if (i_wb_ack)
	begin
		if (r_readptr[WBLSB-3:0] == 0)
			{ sreg, M_DATA } <= { {(BUSDW){1'b0}}, i_wb_data };
		else if (OPT_LITTLE_ENDIAN)
			{ sreg, M_DATA } <= ({ i_wb_data, {(BUSDW){1'b0}} }
						>> (32*r_readptr[WBLSB-3:0]))
					| { {(BUSDW){1'b0}}, sreg };
		else // if (!OPT_LITTLE_ENDIAN)
			{ M_DATA, sreg } <= ({ {(BUSDW){1'b0}}, i_wb_data }
						<< (32*r_readptr[WBLSB-3:0]))
					| { sreg, {(BUSDW){1'b0}} };

		if (!full_return && OPT_LOWPOWER)
			M_DATA <= 0;
	end else if (false_ack)
	begin
		if (OPT_LITTLE_ENDIAN)
			{ sreg, M_DATA } <= { {(BUSDW){1'b0}}, sreg };
		else // if (!OPT_LITTLE_ENDIAN)
			{ M_DATA, sreg } <= { sreg, {(BUSDW){1'b0}} };

	end
	// }}}

	// M_LAST
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		M_LAST <= 0;
	else
		M_LAST <= (return_len <= BUSDW/8);
	// }}}

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, wide_readptr, rd_wb_addr, wide_next_rdlen };
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	F_LGDEPTH = LGPIPE+1;
	reg	f_past_valid;
	wire	[F_LGDEPTH-1:0]	fwr_nreqs, fwr_nacks,
				frd_nreqs, frd_nacks,
				fwr_outstanding, frd_outstanding;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	fwb_master #(
		.AW(AW), .DW(BUSDW), .F_LGDEPTH(F_LGDEPTH)
	) fwb (
		// {{{
		.i_clk(i_clk),
		.i_reset(i_reset),
		//
		.i_wb_cyc( o_wb_cyc),
		.i_wb_stb( o_wb_stb),
		.i_wb_we(  1'b0 ),
		.i_wb_addr( rd_wb_addr),
		.i_wb_data( o_wb_data),
		.i_wb_sel(  o_wb_sel ),
		.i_wb_stall(i_wb_stall),
		.i_wb_ack(  i_wb_ack),
		.i_wb_idata(i_wb_data),
		.i_wb_err(  i_wb_err),
		//
		.fwb_nreqs(frd_nreqs),
		.fwb_nacks(frd_nacks),
		.fwb_outstanding(frd_outstanding)
		// }}}
	);

	always @(*)
	if (o_wb_cyc)
		assert(frd_outstanding == rd_outstanding);

`endif
// }}}
endmodule
