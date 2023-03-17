////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/pktvfifowr.v
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
module	pktvfifowr #(
		// {{{
		parameter	BUSDW = 512,
		parameter	AW = 30-$clog2(BUSDW/8),
		parameter	LGPIPE = 6,
		parameter [0:0]	OPT_LOWPOWER = 1,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 0
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Control port
		// {{{
		input	wire			i_cfg_reset_fifo, i_cfg_mem_err,
		input	wire	[AW-1:0]	i_cfg_baseaddr,
		input	wire	[AW-1:0]	i_cfg_memsize,
		input	wire	[AW+WBLSB-3:0]	i_readptr,
		input	wire			i_pktfull,
		output	wire	[AW+WBLSB-3:0]	o_writeptr,
		output	wire			o_pktwr_stb,
		// }}}
		// Incoming packet
		// {{{
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[BUSDW-1:0]	S_DATA,
		input	wire [$clog2(BUSDW/8)-1:0] S_BYTES,
		input	wire			S_LAST,
		input	wire			S_ABORT,
		// }}}
		// DMA bus interface
		// {{{
		output	reg			o_wb_cyc, o_wb_stb,
		output	wire			o_wb_we,
		output	wire	[AW-1:0]	o_wb_addr,
		output	reg	[BUSDW-1:0]	o_wb_data,
		output	reg	[BUSDW/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall,
		input	wire			i_wb_ack,
		// input wire	[BUSDW-1:0]	i_wb_data,
		input	wire			i_wb_err
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	// Local parameters
	// {{{
	localparam	WBLSB = $clog2(BUSDW/8);

	localparam	[2:0]	WR_CLEARPTR = 3'h0,
				WR_PUSH     = 3'h1,
				WR_FLUSH    = 3'h2,
				WR_NULL     = 3'h3,
				WR_LENGTH   = 3'h4,
				WR_CLEARBUS = 3'h5,
				WR_OVERFLOW = 3'h6;
	// }}}

	reg	[AW+WBLSB-1:0]	wide_baseaddr, wide_memsize,
				wide_writeptr,
				wide_end_of_memory, wide_bytes;
	reg	[31:0]		wide_pktlen;

	// r_writeptr always points to the length word of a packet, minus
	//   the last two bits (which are assumed to be zero, as the length
	//   is guaranteed to be 32b aligned).
	reg	[AW+(WBLSB-2)-1:0]	r_writeptr, r_end_of_packet;
	reg	[AW+WBLSB-1:0]		w_next_dataptr;

	reg	[AW-1:0]	end_of_memory;

	reg	[LGPIPE:0]	wr_outstanding;
	reg	[2*BUSDW-1:0]	next_dblwide_data;
	reg	[2*BUSDW/8-1:0]	next_dblwide_sel;
	reg	[BUSDW-1:0]	next_wr_data;
	reg	[BUSDW/8-1:0]	next_wr_sel;
	reg	[$clog2(BUSDW/8)-1:0]	wide_words, wide_shift;

	reg			lastack;

	reg	[AW+WBLSB-3:0]	wr_wb_addr;

	reg	[AW+WBLSB-1:0]	next_wbaddr, next_wbfirst, next_wbnull;
	reg	[AW+WBLSB-1:0]	wr_pktlen;
	reg	[2:0]		wr_state;
	reg			wr_midpkt;

	reg	[AW+(WBLSB-2)-1:0]		w_mem_fill;
	reg			mem_full, mem_overflow;
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
		// Base address and memsize are both bus word aligned
		wide_baseaddr = 0;
		wide_baseaddr = { i_cfg_baseaddr, {(WBLSB){1'b0}} };

		wide_memsize  = 0;
		wide_memsize  = { i_cfg_memsize, {(WBLSB){1'b0}} };

		// Write and read pointers are 32-bit aligned
		wide_writeptr = 0;
		wide_writeptr = { r_writeptr, 2'b00 };
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write incoming packets to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		wide_words = (S_BYTES + 3) >> 2;
		wide_shift = -wide_words;
		wide_shift[$clog2(BUSDW/8)-1:0] = 0;
	end

	// next_wbaddr
	// {{{
	// Full ADDRESS_WIDTH, AW + WBLSB
	always @(*)
	begin
		next_wbaddr = { wr_wb_addr, 2'b00 } + (BUSDW/8);
		if (next_wbaddr > (wide_baseaddr + wide_memsize))
			next_wbaddr = { wr_wb_addr, 2'b00 } - wide_memsize;
		next_wbaddr[WBLSB-1:0] = { wr_wb_addr[WBLSB-3:0], 2'b00 };
	end
	// }}}

	// next_wbnull
	// {{{
	always @(*)
	begin
		// Points to the length word following the current packet.
		//	Given that writeptr points to the length word of the
		//	current packet, we need to add both the packet length
		//	and the 4-byte length word to get to this location.
		next_wbnull = wide_writeptr + wr_pktlen + 4 + 3;
		next_wbnull[1:0] = 2'b00;
		if (next_wbnull >= wide_end_of_memory)
			next_wbnull[AW+WBLSB-1:WBLSB]
				= next_wbnull[AW+WBLSB-1:WBLSB]
					- wide_memsize[AW+WBLSB-1:WBLSB];
	end
	// }}}

	// next_wbfirst
	// {{{
	// Full byte address
	always @(*)
	begin
		// r_writeptr points to the length word of a packet, so we
		// need something to point us to the first data word of
		// the packet.  That's next_wbfirst.
		next_wbfirst = wide_writeptr + 4;
		next_wbfirst[1:0] = 2'b00;	// Shouldn't need saying
		if (next_wbfirst >= wide_end_of_memory)
			next_wbfirst = { i_cfg_baseaddr, {(WBLSB){1'b0}} };
	end
	// }}}

	// next_dblwide_data, next_dblwide_sel
	// {{{
	always @(*)
	if (OPT_LITTLE_ENDIAN)
	begin
		next_dblwide_data = 0;
		next_dblwide_sel  = 0;

		next_dblwide_data = { {(BUSDW){1'b0}}, S_DATA }
						<< (wr_wb_addr[WBLSB-3:0] * 32);
		if (S_BYTES == 0)
			next_dblwide_sel = { {(BUSDW/8){1'b0}},
							{(BUSDW/8){1'b1}} };
		else
			next_dblwide_sel[BUSDW/8-1:0]
				= {(BUSDW/8){1'b1}} >> (4*wide_shift);

		next_dblwide_data[BUSDW-1:0]
			= next_dblwide_data[BUSDW-1:0]	| next_wr_data;

		next_dblwide_sel[BUSDW/8-1:0]
			= next_dblwide_sel[BUSDW/8-1:0]	| next_wr_sel;
	end else begin
		next_dblwide_data = { S_DATA, {(BUSDW){1'b0}} }
						>> (wr_wb_addr[WBLSB-3:0] * 32);

		next_dblwide_sel = {(BUSDW/4){1'b0}};
		if (S_BYTES == 0)
			next_dblwide_sel = { {(BUSDW/8){1'b1}},
							{(BUSDW/8){1'b0}} };
		else
			next_dblwide_sel[2*BUSDW/8-1:BUSDW/8]
				= {(BUSDW/8){1'b1}} << (4*wide_shift);
		next_dblwide_sel = next_dblwide_sel >> (wr_wb_addr[1:0] * 32);

		next_dblwide_data[BUSDW-1:0]
			= next_dblwide_data[BUSDW-1:0]	| next_wr_data;

		next_dblwide_sel[BUSDW/8-1:0]
			= next_dblwide_sel[BUSDW/8-1:0]	| next_wr_sel;
	end
	// }}}

	// wr_pktlen
	// {{{
	always @(*)
	begin
		wide_bytes = 0;
		wide_bytes[$clog2(BUSDW/8)-1:0] = S_BYTES;
	end

	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err)
	begin
		wr_pktlen <= 0;
	end else if (S_ABORT && (!S_VALID || S_READY))
	begin
		wr_pktlen <= 0;
	end else if (S_VALID && S_READY)
	begin
		if (!wr_midpkt)
			wr_pktlen <= (1<<(BUSDW/8));
		else if (S_BYTES == 0)
			wr_pktlen <= wr_pktlen + (1<<(BUSDW/8));
		else
			wr_pktlen <= wr_pktlen + wide_bytes;
	end

	always @(*)
	begin
		wide_pktlen = 0;
		wide_pktlen[AW+WBLSB-1:0] = wr_pktlen;
	end
	// }}}

	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err
						|| (o_wb_cyc && i_wb_err))
	begin
		// {{{
		o_wb_cyc  <= 0;
		o_wb_stb  <= 0;
		wr_wb_addr <= 0;
		o_wb_data <= 0;
		o_wb_sel  <= 0;
		r_writeptr <= { i_cfg_baseaddr, {(WBLSB-2){1'b0}} };
		wr_state <= WR_CLEARPTR;
		// wr_pktstart <= i_cfg_baseaddr;
		// }}}
	end else case(wr_state)
	WR_CLEARPTR: begin
		// {{{
		if (!o_wb_stb || !i_wb_stall)
		begin
			// Write a NULL word to the beginning of memory
			o_wb_cyc  <= 1'b1;
			o_wb_stb  <= 1'b1;
			wr_wb_addr <= r_writeptr;
			// r_pktstart <= r_writeptr;
			o_wb_data <= 0;
			if (OPT_LITTLE_ENDIAN)
			begin
				o_wb_sel <= { {(BUSDW/8-4){1'b0}}, 4'hf }
					<< (32*r_writeptr[WBLSB-3:0]);
			end else begin
				o_wb_sel <= { 4'hf, {(BUSDW/8-4){1'b0}} }
					>> (32*r_writeptr[WBLSB-3:0]);
			end
			wr_state   <= WR_PUSH;
		end end
		// }}}
	WR_PUSH: begin
		// {{{
		if (S_ABORT && (!S_VALID || S_READY))
			wr_midpkt <= 1'b0;

		if (!o_wb_stb || !i_wb_stall)
		begin
			if (lastack)
				o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;

			if (S_ABORT || !wr_midpkt)
			begin
				wr_wb_addr <= next_wbfirst[AW+WBLSB-1:2];
				wr_midpkt <= 1'b0;
			end else if (o_wb_stb)
				wr_wb_addr <= next_wbaddr[AW+WBLSB-1:2];
		end

		if ((!o_wb_stb || !i_wb_stall) && S_VALID && S_READY && !S_ABORT)
		begin
			wr_midpkt <= 1'b1;
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b1;

			if (OPT_LITTLE_ENDIAN)
			begin
				{ next_wr_data, o_wb_data }<=next_dblwide_data;
				{ next_wr_sel,  o_wb_sel  }<=next_dblwide_sel;
			end else begin
				{ o_wb_data, next_wr_data }<=next_dblwide_data;
				{ o_wb_sel,  next_wr_sel  }<=next_dblwide_sel;
			end

			if (S_LAST)
				wr_state <= WR_FLUSH;
		end else if (mem_overflow)
			wr_state <= WR_OVERFLOW;
		end
		// }}}
	WR_FLUSH: begin
		// {{{
		if (!o_wb_stb || !i_wb_stall)
		begin
			wr_midpkt <= 1'b0;

			if (o_wb_stb)
				wr_wb_addr <= next_wbaddr[AW+WBLSB-1:2];

			if (lastack)
				o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;

			if (next_wr_sel != 0)
				{ o_wb_cyc, o_wb_stb } <= 2'b11;

			o_wb_data   <= next_wr_data;
			o_wb_sel    <= next_wr_sel;
			next_wr_data <= {(BUSDW  ){1'b0}};
			next_wr_sel  <= {(BUSDW/8){1'b0}};

			wr_state <= WR_NULL;
		end end
		// }}}
	WR_NULL: begin // Write a concluding 32-bit NULL word
		// {{{
		if (!o_wb_stb || !i_wb_stall)
		begin
			wr_midpkt <= 1'b0;

			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			wr_wb_addr <= next_wbnull[AW+WBLSB-1:2];
			o_wb_data   <= {(BUSDW){1'b0}};
			if (OPT_LITTLE_ENDIAN)
			begin
				o_wb_sel <= { {(BUSDW/8-4){1'b0}}, 4'hf }
					<< (4*r_writeptr[WBLSB-3:0]);
			end else begin
				o_wb_sel <= { 4'hf, {(BUSDW/8-4){1'b0}} }
					>> (4*r_writeptr[WBLSB-3:0]);
			end
			next_wr_data <= {(BUSDW  ){1'b0}};
			next_wr_sel  <= {(BUSDW/8){1'b0}};

			wr_state <= WR_LENGTH;
		end end
		// }}}
	WR_LENGTH: begin // Write the length word for the packet
		// {{{
		if (!o_wb_stb || !i_wb_stall)
		begin
			wr_midpkt <= 1'b0;

			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			wr_wb_addr <= r_writeptr;
			r_writeptr <= next_wbnull[AW+WBLSB-1:2];

			if (!OPT_LOWPOWER)
				o_wb_data   <= {(BUSDW/32){wide_pktlen}};
			else if (OPT_LITTLE_ENDIAN)
				o_wb_data   <= { {(BUSDW-32){1'b0}}, wide_pktlen } << (32*r_writeptr[WBLSB-3:0]);
			else
				o_wb_data   <= { wide_pktlen, {(BUSDW-32){1'b0}} } >> (32*r_writeptr[WBLSB-3:0]);

			if (OPT_LITTLE_ENDIAN)
			begin
				o_wb_sel <= { {(BUSDW/8-4){1'b0}}, 4'hf }
					<< (r_writeptr[WBLSB-3:0] * 4);
			end else begin
				o_wb_sel <= { 4'hf, {(BUSDW/8-4){1'b0}} }
					>> (r_writeptr[WBLSB-3:0] * 4);
			end
			next_wr_data <= {(BUSDW  ){1'b0}};
			next_wr_sel  <= {(BUSDW/8){1'b0}};

			wr_state <= WR_CLEARBUS;
		end end
		// }}}
	WR_CLEARBUS: begin // Write for last ACK to know the packet was written
		// {{{
		if (!o_wb_stb || !i_wb_stall)
		begin
			if (lastack)
				o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end
		if (!o_wb_stb && (wr_outstanding == (i_wb_ack ? 1:0)))
			wr_state <= WR_PUSH;
		end
		// }}}
	WR_OVERFLOW: begin // No room in memory.  Wait for the pkt to complete
		// {{{
		if (S_VALID && S_READY && S_LAST)
			wr_midpkt <= 1'b0;
		if (S_ABORT && (!S_VALID || S_READY))
			wr_midpkt <= 1'b0;
		if (!o_wb_stb || !i_wb_stall)
		begin
			if (lastack)
				o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end

		if (!wr_midpkt && !o_wb_stb
					&& (wr_outstanding == (i_wb_ack ? 1:0)))
			wr_state <= WR_PUSH;
		end
		// }}}
	default: begin
		// {{{
`ifdef	FORMAL
		assert(0);
`endif
		end
		// }}}
	endcase

	// lastack
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err || !o_wb_cyc)
		lastack <= 1;
	else
		lastack <= (wr_outstanding + (o_wb_stb ? 1:0)
						- (i_wb_ack ? 1:0)) <= 1;
`ifdef	FORMAL
	// Should always be true when we need to drop CYC, on the cycle
	//   containing the last acknowledgment associated with all of our
	//   requests.
	always @(*)
	if (o_wb_cyc)
		assert(lastack == (wr_outstanding
				+ (o_wb_stb ? 1:0) <= (i_wb_ack ? 1:0)));
`endif
	// }}}

	// wr_outstanding
	// {{{
	initial	wr_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err || !o_wb_cyc)
		wr_outstanding <= 0;
	else case ({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b10: wr_outstanding <= wr_outstanding + 1;
	2'b01: wr_outstanding <= wr_outstanding - 1;
	default: begin end
	endcase
`ifdef	FORMAL
	always @(*)
	if (!o_wb_stb && wr_outstanding == 0)
		assert(!o_wb_cyc);
`endif
	// }}}

	assign	S_READY = ((wr_state == WR_PUSH)
				&& (!o_wb_stb || i_wb_stall)
				&& i_pktfull
				&& !mem_full && !wr_outstanding[LGPIPE])
			|| (wr_state == WR_OVERFLOW && wr_midpkt);

	assign	o_wb_addr = wr_wb_addr[AW+(WBLSB-2)-1:(WBLSB-2)];
	assign	o_wb_we = 1'b1;
	assign	o_writeptr = r_writeptr;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory fill tracking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
		end_of_memory <= i_cfg_baseaddr + i_cfg_memsize;

	always @(*)
		wide_end_of_memory = { end_of_memory, {(WBLSB){1'b0}} };

	// r_end_of_packet, w-next_dataptr
	// {{{
	// w_next_dataptr is a byte address
	always @(*)
	begin
		// Points to where the next data packet would begin from.
		// Verilator lint_off WIDTH
		w_next_dataptr = wide_writeptr + { wr_pktlen, 2'b00 } + 8 + 3;
		// Verilator lint_on  WIDTH
		w_next_dataptr[1:0] = 2'b00;
		if (w_next_dataptr >= wide_end_of_memory)
			w_next_dataptr = w_next_dataptr - wide_memsize;
	end

	// 32b address
	always @(posedge i_clk)
	if (i_cfg_reset_fifo)
		r_end_of_packet <= { i_cfg_baseaddr, {(WBLSB-2){1'b0}} };
	else
		r_end_of_packet <= w_next_dataptr[AW+WBLSB-1:2];
	// }}}

	always @(*)
	begin
		w_mem_fill = (r_end_of_packet - i_readptr) + ((1<<(WBLSB-2))-1);
		if (i_readptr > r_end_of_packet)
			w_mem_fill = w_mem_fill + { i_cfg_memsize, {(WBLSB-2){1'b0}} };
	end

	always @(posedge i_clk)
	if (i_cfg_reset_fifo)
		mem_full <= 0;
	else
		mem_full <= (w_mem_fill[(WBLSB-2) +: AW] >= i_cfg_memsize);

	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || wr_state != WR_PUSH)
		mem_overflow <= 1'b0;
	else
		mem_overflow <= mem_full && S_VALID;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Count available packets in memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	o_pktwr_stb = (wr_state == WR_CLEARBUS && !o_wb_stb)
			&& (wr_outstanding == (i_wb_ack ? 1:0));

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

	always @(*)
	begin
		wide_readptr  = 0;
		wide_readptr  = { i_readptr, 2'b00 };
	end
	////////////////////////////////////////////////////////////////////////
	//
	// Config: Base address, memsize, memfull
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg	[AW-1:0]	fc_baseaddr, fc_memsize;
	wire	[AW+WBLSB-1:0]	wide_memfill;

	always @(*)
	if (i_reset)
		assume(i_cfg_reset_fifo);

	always @(posedge i_clk)
	if (i_reset || $past(i_reset))
	begin
		assume(!i_cfg_mem_err);
	end else if ($past(i_cfg_reset_fifo))
	begin
		assume(i_cfg_reset_fifo || !i_cfg_mem_err);
		assume(!$rose(i_cfg_mem_err));
	end else if ($past(i_cfg_mem_err))
		assume(i_cfg_reset_fifo);


	always @(*)
	begin
		assume(fc_baseaddr + fc_memsize <= (1<<AW));
		assume(fc_memsize >= 2);

		wide_memfill = wide_writeptr - wide_readptr;
		if (wide_writeptr < wide_readptr)
			wide_memfill = wide_memfill + fc_memsize;
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo)
	begin
		assume(i_cfg_baseaddr == fc_baseaddr);
		assume(i_cfg_memsize  == fc_memsize);
		assume(wide_readptr >= wide_baseaddr);
		assume(wide_readptr <  wide_baseaddr + wide_memsize);
	end

	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo && !$past(i_cfg_reset_fifo))
	begin
		assume((wide_readptr <= $past(wide_readptr) + (DW/8));
		if ($past(wide_readptr)+ (DW/8) >= wide_baseaddr + wide_memsize)
		begin
			assume(wide_readptr <= $past(wide_readptr) + (DW/8)
							- wide_memsize);
		end else begin
			assume((wide_readptr >= $past(wide_readptr));
			assume((wide_readptr <= $past(wide_readptr) + (DW/8));
		end

		assert(wide_memfill <= wide_memsize);
	end

	always @(posedge i_clk)
	if (!i_reset && $past(i_reset || i_cfg_reset_fifo) && !i_cfg_reset_fifo)
	begin
		assume(wide_readptr  == wide_baseaddr);
		assert(wide_writeptr == wide_baseaddr);
		assert(wide_memfill  == 0);
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo)
		assert(pktlen + 8 <= wide_memsize);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// WB
	fwb_master #(
		.AW(AW), .DW(BUSDW), .F_LGDEPTH(F_LGDEPTH)
	) fwb_wr (
		// {{{
		.i_clk(i_clk),
		.i_reset(i_reset),
		//
		.i_wb_cyc( o_wb_cyc),
		.i_wb_stb( o_wb_stb),
		.i_wb_we(  1'b1 ),
		.i_wb_addr( o_wb_addr),
		.i_wb_data( o_wb_data),
		.i_wb_sel(  o_wb_sel ),
		.i_wb_stall(i_wb_stall),
		.i_wb_ack(  i_wb_ack),
		.i_wb_idata({(BUSDW){1'b0}}),
		.i_wb_err(  i_wb_err),
		//
		.fwb_nreqs(fwr_nreqs),
		.fwb_nacks(fwr_nacks),
		.fwb_outstanding(fwr_outstanding)
		// }}}
	);

	always @(*)
	if (!i_reset && !o_wb_stb)
		assert(wr_outstanding == fwr_outstanding);
`endif
// }}}
endmodule
