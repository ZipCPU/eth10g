////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/pktvfiford.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is the second half, the *read* half of the Virtual Packet
//		FIFO.  Packets are defined by some number of bytes, with both
//	start and LAST (i.e. end).  Packets are assumed to be stored in memory,
//	starting with a 32-bit word containing the number of bytes in the
//	packet, followed by the packet data and then the 32-bit length word of
//	the next packet.  A length word of zero is evidence there are no (more)
//	packets present in memory.  The memory region is circular, so packets
//	may start before the end of the memory, and end after wrapping around
//	from the beginning.  This IP depends upon knowing where the write
//	pointer is (from the write half of the Virtual Packet FIFO) know when
//	to read the packet length from memory.  Hence, the write pointer must
//	always point to a valid (or empty) packet length word.
//
//	Note that the four bytes of the packet length word, preceeding a
//	packet, are not counted in the packet's length.
//
// Parameter configuration:
//	BUSDW		The data width of the Wishbone bus (in bits).  Must be
//			at least 32 bits.
//
//	AW		The word address width of the Wishbone bus.  This does
//			not reflect any bits required to represent the bytes
//			within a bus word.
//
//	LGFIFO		The log based two size of the external FIFO.  The
//			external FIFO must hold (1<<LGFIFO) entries.
//
//	LGPIPE		The log based two of the number of bus transactions
//			that may ever be outstanding at any given time.  This
//			should probably be set to the maximum bus latency.
//			When using the MIG, LGPIPE=5 is typically sufficient.
//
//			Since every item requested on the bus must have an
//			allocated entry in the FIFO, LGPIPE should be no larger
//			than LGFIFO.
//
//	MINLEN		The minimum packet length allowed.  This is typically
//			64 bytes, the minimum size of an Ethernet packet.
//			This value *MUST* be greater than zero.
//
//	MAXLEN		The maximum packet length allowed.  Packets larger than
//			MAXLEN will generate an internal reset condition,
//			reflected by o_fifo_err.  This is meant to be a failsafe
//			check on the memory.
//
//	OPT_LOWPOWER	If set, unused values will be forced to zero.
//
//	OPT_LITTLE_ENDIAN	True if the WB bus is implemented in a little
//			endian fashion.
// Configuration:
//	i_cfg_reset_fifo	True if/when the FIFO is being reconfigured,
//			or the base address or memory size are not (yet)
//			valid.
//
//	i_cfg_baseaddr	Points to the word address (bus aligned) of the
//			beginning of the memory region.
//
//	i_cfg_memsize	This size of the allocated memory region, in bus words.
//			(Not bytes)  The memory region must be bus aligned.
//			The base address plus the memory size shall point to
//			one word past the end of memory.  Hence, if memory has
//			only two words (really too small), the base address
//			might be zero and the memsize two.
//
// Operation:
//	o_readptr	A memory pointer to a 32-bit word in memory.  The 2 LSBs
//			are inferred, but not included.  The pointer is used by
//			the other half (the write half) of the FIFO to
//			determine when/if the FIFO is full.  Hence, the write
//			half will never pass the read pointer.  The two
//			pointers, o_readptr and i_writeptr, will only ever be
//			equal when the FIFO is empty.
//
//	i_writeptr	Points to the length word the virtual packet FIFO
//			write half is looking at.  This length word will be
//			zero.  A new packet may be read if ever 1) the read
//			half is idle, and waiting to read a new packet length,
//			and 2) the write pointer is not equal to the read
//			pointer.
//
//	o_fifo_err	This is a check on both the packet length and the write
//			pointer.  Should an invalid packet length ever be read,
//			this FIFO error flag will be set.  The external FIFO
//			*must* be reset at this time.  Examples of invalid
//			lengths include zero length packets, packet lengths
//			longer than the memory size, or even packet lengths
//			longer than the distance to the write pointer.
//			Likewise, this pointer will also be raised if the
//			write pointer ever goes outside the bounds required by
//			the i_cfg_baseaddr and i_cfg_memsize.
//
//			This is intended to be a self-clearing condition.
//			When/if o_fifo_err is ever raised, the virtual FIFO
//			reader will clear its internal state machine and set
//			the read pointer to the current write pointer.  No
//			external action is required, save to clear the external
//			FIFO on this signal.
//
//	WB		A Wishbone master interface, used to read from memory.
//
//	M_*		The outgoing AXI network packet stream interface.
//			Unlike a full featured network packet stream, this
//			interface does not support READY, nor does it ever
//			generate an ABORT.
//
//	i_fifo_rd	The output of this module goes directly into a FIFO.
//			This FIFO shall have (1<<LGFIFO) entries.  Since
//			Wishbone has no ability to handle back pressure, we
//			have to guarantee (internally) that we never issue more
//			WB requests than the FIFO can hold.  Hence, we keep
//			track of how much space is available in the FIFO.
//			When a read request is issued, we decrement from the
//			space available, and when *i_fifo_rd* is true we add
//			one to the space available.
//
//			LGPIPE determines the number of WB transactions we
//			allow to be outstanding (1<<LGPIPE).  There is no reason
//			for this number ever to be larger than the FIFO, so
//			we also insist that LGFIFO >= LGPIPE.
//
//			Also, when either i_reset, i_cfg_reset_fifo, or
//			o_fifo_err are true, the FIFO shall be cleared and any
//			partially generated packets ABORTed (further down in
//			the pipeline.)
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
`timescale	1ns / 1ps
`default_nettype none
// }}}
module	pktvfiford #(
		// {{{
		parameter	BUSDW = 512,
		parameter	AW = 24-$clog2(BUSDW/8),
		parameter	LGFIFO = 5,
		parameter	LGPIPE = 6,
		// MINLEN: A minimum packet length in bytes.  Packets lengths
		// shorter than MINLEN will generate a FIFO error.
		parameter	MINLEN = 64,	// Must be > 0
		// MAXLEN: A maximum packet length in bytes.  Packets lengths
		// greater than MAXLEN will generate a FIFO error.
		parameter	MAXLEN = 65535, // (1<<(AW+$clog2(BUSDW/8))),
		parameter [0:0]	OPT_LOWPOWER = 1,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 0,
		localparam	WBLSB = $clog2(BUSDW/8)
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Control port
		// {{{
		input	wire			i_cfg_reset_fifo,
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
		// No backpressure supt here.  Back pressure handling is via the
		// i_fifo_rd pin, and counting the number of items used in the
		// FIFO internally.
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
	localparam	[1:0]	RD_IDLE      = 2'h0,
				RD_SIZE      = 2'h1,
				RD_PACKET    = 2'h2,
				RD_CLEARBUS  = 2'h3;
	localparam	LCLGPIPE = (LGPIPE <= LGFIFO) ? LGPIPE : LGFIFO;
	// }}}

	// Because we work with so many different types of pointers here,
	// the units are different all over the place, those with the wide_*
	// prefix are *octet* (i.e. 8-bit) pointers.
	reg	[AW+WBLSB-1:0]	wide_baseaddr, wide_memsize, // wide_writeptr
				wide_readptr;

	// The end of memory may require an extra bit, to capture the case where
	// we run right up to the last word in memory.
	reg	[AW+WBLSB:0]	end_of_memory;

	// The following three pointers are 32-bit word pointers, so the
	// bottom 2-LSBs are assumed to be zero, and not included in the
	// pointer.
	reg	[AW+(WBLSB-2)-1:0]	r_readptr, rd_wb_addr, r_endptr;

	reg	[LCLGPIPE:0]	rd_outstanding;
	wire	[LCLGPIPE:0]	w_rd_outstanding;
	reg			r_lastack, lastack;

	reg	[LGFIFO:0]	fifo_space;

	reg	[AW+WBLSB-1:0]	rd_pktlen;
	(* keep *) reg	[31:0]		next_rdlen;
	reg	[1:0]		rd_state;
	(* keep *) reg	[BUSDW-1:0]	wide_next_rdlen;

	reg	[AW+WBLSB:0]	next_rdaddr, next_rdptr,
				next_endptr, step_rdptr;

	reg			dly_check, dly_fifo_err;
	reg	[AW+WBLSB-1:0]	mem_fill;

	wire			full_return, false_ack, full_stb;
	reg	[AW+WBLSB-1:0]	return_len, next_return_len;
	wire	[BUSDW/8-1:0]	ptrsel;

	wire	fifo_commit;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Control logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Most of our control logic is found in the parent module.  Expanding
	// our pointers to full byte-addresses is all that's left for us to do
	// here.  This just converts us to a common set of units, for following
	// pointer arithmetic.
	//

	always @(*)
	begin
		wide_baseaddr = 0;
		wide_baseaddr = { i_cfg_baseaddr, {(WBLSB){1'b0}} };

		wide_memsize  = 0;
		wide_memsize  = { i_cfg_memsize, {(WBLSB){1'b0}} };

		wide_readptr  = 0;
		wide_readptr  = { r_readptr, 2'b00 };

		// wide_writeptr  = 0;
		// wide_writeptr  = { i_writeptr, 2'b00 };
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read packets back out from memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// This is our main read-from-memory FSM handling section.  We start
	// with some combinatorial pointer math, before getting to the FSM
	// itself.

	generate if (BUSDW == 32)
	begin : BASIC_WIDE_RDLEN
		always @(*)
			wide_next_rdlen = i_wb_data;
	end else if (OPT_LITTLE_ENDIAN)
	begin : BASIC_LILRDLEN
		always @(*)
			wide_next_rdlen = i_wb_data >> (32*r_readptr[WBLSB-3:0]);
	end else begin : BASIC_BIGRDLEN
		always @(*)
			wide_next_rdlen = i_wb_data << (32*r_readptr[WBLSB-3:0]);
	end endgenerate

	always @(*)
	if (OPT_LITTLE_ENDIAN)
		next_rdlen = wide_next_rdlen[31:0];
	else
		next_rdlen = wide_next_rdlen[BUSDW-32 +: 32];

	// next_rdaddr = rd_wb_addr + BUSDW/8
	// {{{
	// This is a full (octet) address width pointer to the read address
	// plus one bus word (i.e. BUSDW/8 octets).  As with all of the pointers
	// used here, this pointer wraps around the end of memory if necessary.
	// Unlike the next_rdptr, which is very similar, this one is based
	// off of the current read request address, rd_wb_addr, from which we
	// grab the top AW bits to get o_wb_addr.
	always @(*)
	begin
		next_rdaddr = { rd_wb_addr, 2'b00 } + BUSDW/8;

		if (next_rdaddr >= end_of_memory)
			next_rdaddr = next_rdaddr - { i_cfg_memsize, {(WBLSB){1'b0}} };
	end
	// }}}

	// next_rdptr = r_readptr + BUSDW/8
	// {{{
	// A full (octet) address width pointer for the next address in memory,
	// following r_readptr, plus one (full) bus word.  The read pointer will
	// either be set to this address (while reading through packets), or its
	// address plus 4 (via step_rdptr).  Either way, the read pointer wraps
	// around the end of memory in (what should be) an operation transparent
	// to any user.
	always @(*)
	begin
		next_rdptr = { 1'b0, r_readptr, 2'b00 } + BUSDW/8;

		if (next_rdptr >= end_of_memory)
			next_rdptr = next_rdptr
					- { i_cfg_memsize, {(WBLSB){1'b0}} };
		// if (next_rdptr[WBLSB +: AW] == r_endptr[WBLSB-2 +: AW])
		//	next_rdptr = { 1'b0, r_endptr, 2'b00 };
	end
	// }}}

	// r_endptr, next_endptr
	// {{{
	// A helper to calculate the full byte pointer, pointing to the last
	// valid 32-bit word of the packet in memory.  Since next_rdlen is
	// only valid when (rd_state == RD_SIZE && o_wb_cyc && i_wb_ack),
	// this value will also only be valid at the same time.
	always @(*)
	begin
		next_endptr = { r_readptr, 2'b00 } + next_rdlen[0+: AW+WBLSB]
				+ 3;	// Plus the size of the pointer,-1
		next_endptr[1:0] = 2'b00;
		if (next_endptr >= end_of_memory)
			next_endptr = next_endptr
					- { i_cfg_memsize, {(WBLSB){1'b0}} };
	end

	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || (o_wb_cyc && i_wb_err))
		r_endptr <= { i_cfg_baseaddr, {(WBLSB-2){1'b0}} };
	else if (rd_state == RD_IDLE)
		r_endptr <= r_readptr;
	else if (rd_state == RD_SIZE && i_wb_ack)
		r_endptr <= next_endptr[AW+WBLSB-1:2];
	// }}}

	// step_rdptr = r_readptr + 4
	// {{{
	// step_rdptr is a full (octet) address width.  Here, we calculate
	// the circular pointer address to add one 32-bit value to r_readptr.
	// This can move us from the end of the packet to the length pointer
	// of the packet, or again from the length to the first word of the
	// packet.
	always @(*)
	begin
		step_rdptr = { r_readptr, 2'b00 } + 4;

		if (step_rdptr >= end_of_memory)
			step_rdptr = step_rdptr - { i_cfg_memsize, {(WBLSB){1'b0}} };
	end
	// }}}

	// ptrsel = (first o_wb_sel)
	// {{{
	generate if (BUSDW==32)
	begin : BASIC_PTRSEL
		assign	ptrsel = 4'hf;
	end else if (OPT_LITTLE_ENDIAN)
	begin : WIDE_LILPTRSEL
		assign	ptrsel = { {(BUSDW/8-4){1'b0}}, 4'hf }
					<< (4*r_readptr[WBLSB-3:0]);
	end else begin : WIDE_BIGPTRSEL
		assign	ptrsel = { 4'hf, {(BUSDW/8-4){1'b0}} }
					>> (4*r_readptr[WBLSB-3:0]);
	end endgenerate
	// }}}

	initial	{ o_wb_cyc, o_wb_stb } = 2'b0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || (o_wb_cyc && i_wb_err))
	begin
		// {{{
		o_wb_cyc  <= 0;
		o_wb_stb  <= 0;
		rd_wb_addr <= 0;
		o_wb_sel  <= 0;
		r_readptr <= { i_cfg_baseaddr, {(WBLSB-2){1'b0}} };
		rd_state  <= RD_IDLE;
		rd_pktlen <= 0;
		// }}}
	end else if (o_fifo_err)
	begin
		// {{{
		o_wb_cyc  <= 0;
		o_wb_stb  <= 0;
		rd_wb_addr <= 0;
		o_wb_sel  <= 0;
		r_readptr <= i_writeptr;
		rd_state  <= RD_IDLE;
		rd_pktlen <= 0;
		// }}}
	end else case(rd_state)
	RD_IDLE: begin
		// {{{
		o_wb_cyc  <= 1'b0;
		o_wb_stb  <= 1'b0;
		rd_wb_addr <= r_readptr;
		rd_pktlen  <= 0;

		o_wb_sel <= ptrsel;

		if (!M_VALID && i_writeptr != r_readptr)
		begin
			// Issue a read command to capture the packet length
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			rd_state <= RD_SIZE;
		end end
		// }}}
	RD_SIZE: begin
		// {{{
		rd_pktlen  <= 0;

		if (!i_wb_stall)
			o_wb_stb <= 1'b0;
		if (i_wb_ack)
		begin
			o_wb_cyc <= 1'b0;
			rd_state <= RD_PACKET;

			rd_pktlen  <= next_rdlen[AW+WBLSB-1:0];

			r_readptr  <= step_rdptr[AW+WBLSB-1:2];
			rd_wb_addr <= step_rdptr[AW+WBLSB-1:2];
		end end
		// }}}
	RD_PACKET: begin
		// {{{
		o_wb_sel <= {(BUSDW/8){1'b1}};
		if (!i_wb_stall)
			o_wb_stb <= 1'b0;
		if (lastack)
			o_wb_cyc <= 1'b0;

		// Don't increment the read pointer until the data comes back.
		// That way the writer will know it has clear access to this
		// data, now that it's been fully read and acknowledge.
		if (i_wb_ack)
			r_readptr <= next_rdptr[2 +: AW+(WBLSB-2)];

		if (o_wb_stb && !i_wb_stall)
		begin
			// This address may go too far, stepping once too
			// many times after the last address is corrected.
			// We'll come back and fix this in RD_IDLE later.
			rd_wb_addr   <= next_rdaddr[AW+WBLSB-1:2];
		end

		if (o_wb_stb && o_wb_addr == r_endptr[WBLSB-2 +: AW])
		begin
			rd_state <= RD_CLEARBUS;
		end else if (!o_wb_stb || !i_wb_stall)
		begin
			if (!w_rd_outstanding[LCLGPIPE]
				&& (o_wb_stb || !rd_outstanding[LCLGPIPE-1])
				&& !dly_fifo_err && !dly_check
				&& (o_wb_stb || fifo_space[LGFIFO])
					&& (fifo_space > (o_wb_stb ? 2:1)))
				{ o_wb_cyc, o_wb_stb } <= 2'b11;

		end end
		// }}}
	RD_CLEARBUS: begin
		// {{{
		// We come in here with the last request on the bus, either
		// with o_wb_stb high or it having already been issued.  Our
		// goal here is to deactivate the bus once the entire packet
		// has been requested, and then to go back to wait for the
		// next packet.
		o_wb_sel <= {(BUSDW/8){1'b1}};
		if (!i_wb_stall)
			o_wb_stb <= 1'b0;

		if (o_wb_stb && !i_wb_stall)
		begin
			rd_wb_addr   <= next_rdaddr[AW+WBLSB-1:2];
		end

		if (lastack)
		begin
			o_wb_cyc  <= 1'b0;
			rd_state  <= RD_IDLE;
			// Verilator lint_off WIDTH
			if (((r_endptr + 1)<<2) >= end_of_memory)
				r_readptr <= i_cfg_baseaddr << (WBLSB-2);
				// Verilator lint_on  WIDTH
			else
				r_readptr <= r_endptr + 1;
		end else if (i_wb_ack)
			r_readptr <= next_rdptr[2 +: AW+(WBLSB-2)];
		end
		// }}}
	default: begin end
	endcase
`ifdef	FORMAL
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || o_fifo_err || (o_wb_cyc && i_wb_err))
	begin
	end else case(rd_state)
	RD_IDLE: begin
		assert(!o_wb_cyc);
		assert(rd_outstanding == 0);
		// assert(!i_wb_ack);
		end
	RD_SIZE: begin
		assert(rd_outstanding + (o_wb_stb ? 1:0) == 1);
		if (i_wb_ack)
		begin
			// We don't need to assume a valid length here.
			// The FIFO error logic following will validate
			// it, and generate an error if it's not a valid
			// length.
			//
			// assume(next_rdlen[31:0] > 0);
			// assume(next_rdlen[31:0] + 8
			//		<= { fc_memsize, {(WBLSB){1'b0}} });
		end end
	RD_PACKET: begin end
	RD_CLEARBUS: begin
		// Not quite true.  o_wb_addr will point to one 32-bit word
		// past r_endptr
		if (o_wb_stb || rd_outstanding > 0)
		begin
			if (wide_readptr + { rd_outstanding, {(WBLSB){1'b0}} }
				>= end_of_memory)
			begin
				assert(o_wb_addr == r_readptr[WBLSB-2 +: AW]
						+ rd_outstanding
						- i_cfg_memsize);
			end else
				assert(o_wb_addr == r_readptr[WBLSB-2 +: AW]
						+ rd_outstanding);
		end end
	endcase

	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo && !o_fifo_err)
	begin
		assert(wide_readptr >= wide_baseaddr);
		assert(wide_readptr < wide_baseaddr + wide_memsize);
	end
	// }}}
`endif

	// rd_outstanding
	// {{{
	initial	rd_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || !o_wb_cyc || o_fifo_err)
		rd_outstanding <= 0;
	else case ({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b10: rd_outstanding <= rd_outstanding + 1;
	2'b01: rd_outstanding <= rd_outstanding - 1;
	default: begin end
	endcase

	assign	w_rd_outstanding = rd_outstanding + (o_wb_stb ? 1:0);
	// }}}

	// fifo_space
	// {{{
	assign	fifo_commit = ((o_wb_stb && !i_wb_stall) && full_stb
			&&(rd_state == RD_PACKET || rd_state == RD_CLEARBUS))
		|| false_ack;

	initial	fifo_space = 1<<LGFIFO;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || o_fifo_err)
		fifo_space <= 1<<LGFIFO;
	else case({ fifo_commit, i_fifo_rd })
	2'b10: fifo_space <= fifo_space - 1;
	2'b01: fifo_space <= fifo_space + 1;
	default: begin end
	endcase
`ifdef	FORMAL
	// {{{
	always @(*)
	if (fifo_space >= (1<<LGFIFO))
		assume(!i_fifo_rd);

	always @(*)
	if (!i_reset && (rd_state == RD_PACKET || rd_state == RD_SIZE))
	begin
		assert(!false_ack);
	end

	always @(*)
	if (!i_reset && (rd_state == RD_PACKET || rd_state == RD_CLEARBUS))
	begin
		if (fifo_space >= (1<<LGFIFO)-1-rd_outstanding + (full_return ? 0:1))
		begin
			assume(!i_fifo_rd);
		end

		if (o_wb_stb || rd_outstanding > 0)
		begin
			assert(fifo_space >= 1 + (o_wb_stb ? 1:0));
		end
		assert(fifo_space <= (1<<LGFIFO));
		assert(rd_outstanding <= (1<<LGFIFO));
		assert(fifo_space + rd_outstanding <= (1<<LGFIFO)
						+ (full_return ? 0:1));
	end else if (!i_reset)
	begin
		if (fifo_space >= (1<<LGFIFO))
			assume(!i_fifo_rd);
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && fifo_commit)
		assert(fifo_space >= 0);

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo)
	begin
		assert(fifo_space <= (1<<LGFIFO));
		if (o_wb_stb
			&& (rd_state == RD_PACKET || rd_state == RD_CLEARBUS))
		begin
			assert(fifo_space >= 1);
		end

		if ((rd_state == RD_PACKET && o_wb_stb)
			|| (rd_state == RD_CLEARBUS && (o_wb_stb
						|| rd_outstanding != 0)))
		begin
			assert(fifo_space > 0);
		end
	end

	always @(*)
	if (!i_reset && o_wb_stb
			&& (rd_state == RD_PACKET || rd_state == RD_CLEARBUS))
		assert(fifo_space > 0);
	// }}}
`endif
	// }}}

	assign	o_wb_we   = 1'b0;
	assign	o_wb_data = {(BUSDW){1'b0}};
	assign	o_wb_addr = rd_wb_addr[AW+(WBLSB-2)-1:(WBLSB-2)];

	assign	o_readptr = r_readptr;

	// Last ack -- true when we need to drop CYC
	// {{{
	// We drop CYC for 3 reasons (other than memory errors, resets, etc.)
	// 1. We've read the packet size (CYC is dropped for one cycle)
	// 2. We've reached the end of the packet, and may need to wait for
	//	another packet
	// 3. The FIFO has no space left in it
	//
	// Here, we judge whether we've reached the last acknowledgment
	// before one of these reasons.
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || !o_wb_cyc)
		r_lastack <= 1;
	else
		r_lastack <= (rd_outstanding + ((o_wb_stb && !i_wb_stall) ? 1:0)
				<= (i_wb_ack ? 2:1));
	always @(*)
		lastack = r_lastack && (rd_outstanding[0] + (o_wb_stb ? 1:0)
					== (i_wb_ack ? 1:0));
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory size handling/checking, fifo error generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_fifo_err
	// {{{
	//	Four causes of FIFO errors:
	//	1. A zero length, after we've been told there's something there
	//	2. An oversized packet, larger than either MAXLEN or memsize
	//	3. A packet that passes the write pointer
	//	4. An out of bounds write pointer
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		o_fifo_err <= 1'b0;
	else begin
		o_fifo_err <= 1'b0;
		if (dly_fifo_err)
			o_fifo_err <= 1'b1;
		if ({ 1'b0, i_writeptr, 2'b00 } < wide_baseaddr)
			o_fifo_err <= 1'b1;
		if ({ 1'b0, i_writeptr, 2'b00 } >= end_of_memory)
			o_fifo_err <= 1'b1;
		if (o_wb_cyc && i_wb_ack && rd_state == RD_SIZE)
		begin
			if ({ 1'b0, next_rdlen } + 4 + (1<<WBLSB)
						>= { 2'b0, wide_memsize })
				o_fifo_err <= 1'b1;
			if (AW+WBLSB <= 31 && |next_rdlen[31:AW+WBLSB])
				o_fifo_err <= 1'b1;
			if ({ 1'b0, next_rdlen } < MINLEN)
				o_fifo_err <= 1'b1;
			if ({ 1'b0, next_rdlen } >= MAXLEN)
				o_fifo_err <= 1'b1;
		end
	end
	// }}}

	// dly_check
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || o_fifo_err)
		dly_check <= 1'b0;
	else if (i_wb_ack && rd_state == RD_SIZE)
	begin
		dly_check <= 1'b1;
	end else
		dly_check <= 1'b0;
`ifdef	FORMAL
	always @(*)
	if (!i_reset && (rd_state == RD_IDLE || rd_state == RD_SIZE))
		assert(!dly_check);
`endif
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
	// Packet length verification check: Packets may not be larger than
	// the memory size available to them.  If they are, we'll declare an
	// error (dly_fifo_err, then o_fifo_err on the next clock), and we'll
	// reset locally to the writeptr as a result.
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || o_fifo_err || !dly_check)
		dly_fifo_err <= 1'b0;
	else begin
		dly_fifo_err <= 0;
		if (mem_fill < rd_pktlen + 4)
			// There's no room for this packet in the amount of
			// memory currently filled
			dly_fifo_err <= 1'b1;
	end
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

`ifdef	FORMAL
	wire			f_read_aligned;
	wire	[WBLSB-1:0]	f_read_lsb;
`endif

	// M_VALID
	// {{{
	initial	M_VALID = 1'b0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_SIZE || o_fifo_err)
		M_VALID <= 1'b0;
	else if ((o_wb_cyc && i_wb_ack && full_return) || false_ack)
		M_VALID <= 1'b1;
	else // if (M_READY) -- backpressure not supported
		M_VALID <= 1'b0;
	// }}}

	generate if (BUSDW == 32)
	begin : NO_REALIGNMENT
		assign	full_return = 1'b1;	// All returns are full
		assign	full_stb    = 1'b1;	// All requests go to FIFO
		assign	false_ack   = 1'b0;	// No flushing returns

		// M_DATA (and sreg)
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE
						|| rd_state == RD_SIZE)
			M_DATA <= 0;
		else if (!OPT_LOWPOWER || i_wb_ack)
			M_DATA <= i_wb_data;
		// }}}

		// next_return_len -- how many bytes are left?
		// {{{
		always @(*)
		if (return_len >= BUSDW/8)
			next_return_len = return_len - BUSDW/8;
		else
			next_return_len = 0;
		// }}}

`ifdef	FORMAL
		assign	f_read_aligned = 1'b1;
		assign	f_read_lsb = 2'b00;
`endif
	end else begin: GEN_REALIGNMENT
		reg			r_full_return, r_false_ack, r_full_stb;
		reg	[BUSDW-1:0]	sreg;

		// full_stb
		// {{{
		/*
		always @(*)
		begin
			// rdlen_words = the total number of WB words we need
			//   to read.  This may be one more than the total
			//   number of words in the packet.
			rdlen_words = { 1'b0, next_rdlen[WBLSB-1:0] };
			if (!(&r_readptr[WBLSB-3:0]))
			begin
				rdlen_words = rdlen_words
				  +(((BUSDW-32)/32 - r_readptr[WBLSB-3:0])<<2);
			end
			rdlen_words = rdlen_words + (BUSDW/8-1);
			rdlen_words = rdlen_words >> WBLSB;

			// Let's see if we can simplify this for the Synthesizer
			rdlen_words = ({1'b0,next_rdlen[WBLSB-1:0]}
					+(~{ 1'b0,r_readptr[WBLSB-3:0], 2'b11 })
					+ { 1'b0, {(WBLSB){1'b1}} }
					>= (BUSDW/8)
					) ? 1 : 0;

			// fflen_words = the number of words we'll write to the
			//   FIFO.  This should be *exactly* the total number of
			//   words in the packet.
			// fflen_words = { 1'b0, next_rdlen[WBLSB-1:0] }
			//			+ (BUSDW/8-1);
			// fflen_words = fflen_words >> WBLSB;

			fflen_words = (next_rdlen[WBLSB-1:0] == 0) ? 0 : 1;

			first_stb = (rdlen_words == fflen_words);


			// Can't this be rewritten as something like ...
			// first_stb = next_rdlen[WBLSB-1:0]
			//	>= ((BUSDW-32)/32)-r_readptr[WBLSB-3:0], 2'b00 }) ?
		end
		*/

		always @(posedge i_clk)
		if (i_reset || i_cfg_reset_fifo || o_fifo_err
				|| rd_state == RD_IDLE || rd_state == RD_SIZE)
		begin
			r_full_stb <= (&r_readptr[WBLSB-3:0]);
		end else if (o_wb_stb && !i_wb_stall)
			// After the first, all strobe requests are for
			// a full bus size of data
			r_full_stb <= 1'b1;

		assign	full_stb = r_full_stb;
		// }}}

		// full_return: Should an ACK trigger a full DW/8 output?
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_cfg_reset_fifo || o_fifo_err
				|| rd_state == RD_IDLE || rd_state == RD_SIZE)
			// We only generate a FIFO write on the first return
			// if the lower bits of the read pointer are zero.
			// HOWEVER ... the readptr in both IDLE and RD_SIZE
			// states points to the length word, not the first
			// data word, so we really need to add one, hence
			// we check for all bits being one here.
			r_full_return <= (&r_readptr[WBLSB-3:0]);
		else if (i_wb_ack)
			r_full_return <= 1'b1;

		assign	full_return = r_full_return;
		// }}}

		// false_ack: When do we flush our shift register?
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_cfg_reset_fifo || rd_state == RD_SIZE
					|| o_fifo_err || !i_wb_ack || !lastack)
			// Wrong time to flush, so ... don't
			r_false_ack <= 0;
 		// else if (!lastack || (rd_state == RD_PACKET && !o_wb_stb))
		//	// Can't flush yet, we're not done
		//	r_false_ack <= 0;
		else begin
			// NOW.  Flush if there's more data to return.
			// r_false_ack <= (return_len != 0)
			//		&& (return_len < BUSDW/8);
			r_false_ack <= (return_len > BUSDW/8) && full_return
				&& (rd_state == RD_CLEARBUS || (o_wb_stb
					&& o_wb_addr== r_endptr[WBLSB-2 +: AW]))
					&& (return_len < 2*BUSDW/8);
		end

		assign	false_ack = r_false_ack;
		// }}}

		// M_DATA (and sreg)
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE
							|| rd_state == RD_SIZE)
			{ M_DATA, sreg } <= { sreg, {(BUSDW){1'b0}} };
		else if (i_wb_ack)
		begin
			if (r_readptr[WBLSB-3:0] == 0)
				{ sreg, M_DATA } <= { {(BUSDW){1'b0}}, i_wb_data };
			else if (OPT_LITTLE_ENDIAN)
				{ sreg, M_DATA }
					<= ({ i_wb_data, {(BUSDW){1'b0}} }
						>> (32*r_readptr[WBLSB-3:0]))
					| { {(BUSDW){1'b0}}, sreg };
			else // if (!OPT_LITTLE_ENDIAN)
				{ M_DATA, sreg }
					<= ({ {(BUSDW){1'b0}}, i_wb_data }
						<< (32*r_readptr[WBLSB-3:0]))
					| { sreg, {(BUSDW){1'b0}} };

			if (!full_return && OPT_LOWPOWER)
				M_DATA <= 0;
		end else if (false_ack)
		begin
			M_DATA <= sreg;
			sreg   <= {(BUSDW){1'b0}};
		end
`ifdef	FORMAL
		// {{{
		reg	[BUSDW-1:0]	f_chkzero;
		reg	[WBLSB+2:0]	f_chkshift;

		always @(*)
			f_chkshift = BUSDW-32*r_readptr[WBLSB-3:0];

		always @(*)
		if (r_readptr[WBLSB-3:0] == 0)
		begin
			f_chkzero = 0;
		end else if (OPT_LITTLE_ENDIAN)
		begin
			f_chkzero = (sreg >> f_chkshift);
		end else begin
			f_chkzero = (sreg << f_chkshift);
		end

		always @(*)
		if (!i_reset && (rd_state == RD_PACKET
						|| rd_state == RD_CLEARBUS))
		begin
			if (r_readptr[WBLSB-3:0] == 0)
				assert(sreg == 0);
			assert(0 == f_chkzero);
		end else if (!i_reset && rd_state == RD_SIZE)
			assert(sreg == 0);
		// }}}
`endif
		// }}}

		// next_return_len -- how many bytes are left?
		// {{{
		always @(*)
		if (!full_return)
			next_return_len = return_len - (BUSDW/8)
				+ { {(AW){1'b0}}, r_readptr[WBLSB-3:0],2'b0 };
		else if (return_len >= BUSDW/8)
			next_return_len = return_len - BUSDW/8;
		else
			next_return_len = 0;
		// }}}

`ifdef	FORMAL
		assign	f_read_aligned = (r_readptr[WBLSB-3:0] == 0);
		assign	f_read_lsb = { r_readptr[WBLSB-3:0], 2'b00 };

		always @(*)
		if (!i_reset&&(rd_state == RD_PACKET || rd_state == RD_CLEARBUS)
				&& (rd_outstanding > 0 || full_return))
		begin
			assert(full_stb);
		end

		always @(*)
		if (!i_reset && rd_outstanding == 0)
			assert(full_stb == full_return);
`endif
	end endgenerate

	// return_len: How many more bytes are to be expected?
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE || false_ack)
		return_len <= 0;
	else if (o_wb_cyc && i_wb_ack && rd_state == RD_SIZE)
		return_len <= next_rdlen[AW+WBLSB-1:0];
	else if (o_wb_cyc && i_wb_ack && full_return)
		return_len <= next_return_len;
`ifdef	FORMAL
	// {{{
	// Relate return_len to the difference between r_readptr and r_endptr
	reg	[AW+WBLSB-1:0]	f_endptr, f_startptr, f_pktlen, fw_endptr;

	// f_startptr -- points to the length word's address of the current pkt
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		f_startptr <= { i_cfg_baseaddr, {(WBLSB){1'b0}} };
	else if (rd_state == RD_IDLE || rd_state == RD_SIZE)
		f_startptr <= { r_readptr, 2'b00 };

	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo && !o_fifo_err && rd_state != RD_IDLE
			&& rd_state != RD_SIZE && !dly_check && !dly_fifo_err)
	begin
		assert(f_startptr[WBLSB +: AW] != f_endptr[WBLSB +: AW]);
		assert(return_len <= wide_memsize - (1<<WBLSB)-4);
	end

	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo && rd_state != RD_IDLE)
	begin
		assert(wide_baseaddr <= f_startptr);
		assert(f_startptr < end_of_memory);
		assert(f_startptr[1:0] == 2'b00);

		assert(wide_baseaddr <= { rd_wb_addr, 2'b00 });
		assert({ rd_wb_addr, 2'b00 } < end_of_memory);

		assert(wide_baseaddr <= { r_readptr, 2'b00 });
		assert({ 1'b0, r_readptr, 2'b00 } < end_of_memory);
	end
	// }}}

	// f_pktlen
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || o_fifo_err)
		f_pktlen <= 0;
	else if (rd_state == RD_SIZE && i_wb_ack)
		f_pktlen <= next_rdlen[AW+WBLSB-1:0];

	always @(*)
	begin
		fw_endptr = f_startptr + f_pktlen
				+ 3;	// Plus the size of the pointer,-1
		fw_endptr[1:0] = 2'b00;
		if (fw_endptr >= end_of_memory)
			fw_endptr = fw_endptr
					- { i_cfg_memsize, {(WBLSB){1'b0}} };
	end

	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || o_fifo_err || dly_fifo_err
			|| dly_check)
	begin end else if (rd_state == RD_PACKET || rd_state == RD_CLEARBUS)
	begin
		assert(f_pktlen <= wide_memsize - (1<<WBLSB) - 4);
		assert(return_len <= f_pktlen);
	end
	// }}}

	always @(*)
	begin
		// f_endptr should nominally equal a wide_endptr -- a notional
		// signal that doesn't really exist within this design.  It's
		// used to relate r_readptr to r_endptr.  r_endptr advances
		// on every ACK.  return_len drops on all but the first ack.
		// We can't quite use wide_end_of_packet, since
		// wide_end_of_packet = wide_endptr + 4, so ... not quite the
		// same thing.
		//
		f_endptr = { r_readptr, 2'b00 } + return_len - 1;
		if (!f_read_aligned && full_return)
			// We don't count the first return
			f_endptr = f_endptr - (BUSDW/8);

		if (f_endptr >= end_of_memory)
		begin
			f_endptr = f_endptr- { i_cfg_memsize, {(WBLSB){1'b0}} };
		end

		f_endptr[1:0] = 2'b00;
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && !o_fifo_err && !dly_fifo_err
			&& rd_state == RD_CLEARBUS)
		assert(!o_wb_stb || o_wb_addr == r_endptr[WBLSB-2 +: AW]);

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && !o_fifo_err && !dly_fifo_err)
	case(rd_state)
	RD_IDLE: begin end
	RD_SIZE: begin
		assert(return_len == 0);
		assert(r_endptr == r_readptr);
		end
	default: begin
		assert(return_len <= rd_pktlen);
		if (return_len == 0)
		begin
			assert(!o_wb_stb && rd_outstanding == 0);
		end else // if (full_return)
		begin
			assert(dly_check || !valid_writeptr
				|| ({ r_endptr, 2'b00 } == fw_endptr));
			assert(dly_check || !valid_writeptr || dly_fifo_err
				|| false_ack
				|| f_endptr == fw_endptr);
		end end
	endcase
	// }}}
`endif
	// }}}

	// M_BYTES
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_SIZE || o_fifo_err)
		M_BYTES <= 0;
	else if (return_len >= BUSDW/8)
		M_BYTES <= 0;
	else
		M_BYTES <= return_len[WBLSB-1:0];
	// }}}

	// M_LAST
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || o_fifo_err)
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
	assign	unused = &{ 1'b0, wide_readptr, rd_wb_addr, wide_next_rdlen,
				next_endptr };
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
	localparam	F_LGMAX = $clog2(((MAXLEN*8 + (BUSDW-1))/BUSDW)+1);
	localparam	F_LGDEPTH = LCLGPIPE+1;

	reg	f_past_valid;
	wire	[F_LGDEPTH-1:0]	frd_nreqs, frd_nacks, frd_outstanding;
	(* anyconst *)	reg	[AW-1:0]	fc_baseaddr, fc_memsize;
	(* keep *) reg	[AW+WBLSB:0]	wide_end_of_packet, wide_committed,
				wide_writeptr, wide_endptr;
	wire			valid_writeptr;
	wire	[F_LGMAX-1:0]	fs_word;
	wire	[12-1:0]	fs_packet;
	reg	[AW+WBLSB:0]	fwb_bytes_returned, fwb_bytes_outstanding,
				fwb_next_addr, fwb_wide_request,
				fwb_words_returned, frd_words;
	reg	[AW+WBLSB:0]	fwb_total;
	wire	[WBLSB-1:0]	f_ptroffset;
	reg	[AW+WBLSB-1:0]	f_words_remaining;
	(* keep *) reg	[AW+WBLSB-1:0]	fwb_addr;

	always @(*)
		fwb_addr = { o_wb_addr, {(WBLSB){1'b0}} };


	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	////////////////////////////////////////////////////////////////////////
	//
	// Configuration interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		assume({ 1'b0, fc_baseaddr } + { 1'b0, fc_memsize } <= (1<<AW));
		if (BUSDW == 32)
		begin
			assume(fc_memsize >= 8);
		end else if (BUSDW == 64)
		begin
			assume(fc_memsize >= 4);
		end else begin
			assume(fc_memsize >= 2);
		end
	end

	always @(*)
	begin
		wide_writeptr = 0;
		wide_writeptr = { i_writeptr, 2'b00 };
	end

	assign	valid_writeptr = (wide_writeptr >= wide_baseaddr)
			&&(wide_writeptr < wide_baseaddr + wide_memsize);

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo)
	begin
		assume(i_cfg_baseaddr == fc_baseaddr);
		assume(i_cfg_memsize  == fc_memsize);
	end

	always @(*)
	if (i_reset)
		assume(i_cfg_reset_fifo);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset)&& $past(o_wb_cyc && i_wb_err))
	begin
		assume(i_cfg_reset_fifo);
	end


	always @(posedge i_clk)
	if (f_past_valid && $past(i_cfg_reset_fifo) && !i_cfg_reset_fifo)
	begin
		assume($stable(i_cfg_baseaddr));
		assume($stable(i_cfg_memsize));
	end

	always @(*)
	begin
		wide_committed = wide_writeptr - wide_readptr;
		if (i_writeptr < r_readptr)
			wide_committed = wide_committed
					+ { fc_memsize, {(WBLSB){1'b0}} };
		assume(!valid_writeptr
			|| wide_committed <= { fc_memsize, {(WBLSB){1'b0}} });

		wide_endptr = { 1'b0, r_endptr, 2'b00 };
		wide_end_of_packet = { 1'b0, r_endptr, 2'b00 } + 4;
		if (wide_end_of_packet >= end_of_memory)
			wide_end_of_packet = wide_end_of_packet - wide_memsize;

		// f_wide_pktfill = wide_writeptr - wide_end_of_packet;
		// if (wide_writeptr < wide_end_of_packet)
			// f_wide_pktfill = f_wide_pktfill
					// + { fc_memsize, {(WBLSB){1'b0}} };
	end

	always @(posedge i_clk)
	if (f_past_valid && !i_cfg_reset_fifo && !$past(i_cfg_reset_fifo))
	begin
		assert(end_of_memory == wide_baseaddr + wide_memsize);

		assert(wide_end_of_packet >= wide_baseaddr);
		assert(o_fifo_err || dly_check || (rd_state == RD_IDLE)
			|| wide_end_of_packet <  end_of_memory);

		// assert(f_wide_pktfill <= wide_committed);

		if ($stable(r_readptr))
		begin
			assume(!valid_writeptr
				|| $past(wide_committed) <= wide_committed);
		end else begin
			assume(!valid_writeptr
				|| $past(wide_committed) <= wide_committed - (BUSDW/8));
		end
	end

	always @(posedge i_clk)
	if (f_past_valid && !i_cfg_reset_fifo && !$past(i_cfg_reset_fifo))
		assert($stable(end_of_memory));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone properties
	// {{{

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
		.i_wb_addr( o_wb_addr),
		.i_wb_data( o_wb_data),
		.i_wb_sel(  o_wb_sel ),
		.i_wb_stall(i_wb_stall),
		.i_wb_ack(  i_wb_ack),
		.i_wb_idata(i_wb_data),
		.i_wb_err(  i_wb_err),
		//
		.f_nreqs(frd_nreqs),
		.f_nacks(frd_nacks),
		.f_outstanding(frd_outstanding)
		// }}}
	);

	always @(*)
	if (!i_reset && o_wb_cyc)
		assert(frd_outstanding == rd_outstanding);

	always @(*)
	if (!i_reset && o_wb_stb)
		assert(rd_outstanding <= (1<<LCLGPIPE));

	always @(*)
	if (!i_reset && !o_fifo_err && !i_cfg_reset_fifo && valid_writeptr) // rd_state != RD_IDLE)
	begin
		assert(wide_readptr >= wide_baseaddr);
		assert(wide_readptr <  end_of_memory);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	faxin_master #(
		// {{{
		.DATA_WIDTH(BUSDW),
		// Round down, to the nearest bus word
		.MIN_LENGTH(MINLEN*8/BUSDW),
		// Round up to the next highest bus word
		.MAX_LENGTH((MAXLEN*8 + BUSDW-1)/BUSDW),
		.WBITS($clog2(BUSDW/8)),
		.LGMX(F_LGMAX)
		// }}}
	) faxin (
		// {{{
		.S_AXI_ACLK(i_clk),
		.S_AXI_ARESETN(!i_reset && !i_cfg_reset_fifo && !o_fifo_err),
		//
		.S_AXIN_VALID(M_VALID),
		.S_AXIN_READY(1'b1),
		.S_AXIN_DATA(M_DATA),
		.S_AXIN_BYTES(M_BYTES),
		.S_AXIN_LAST(M_LAST),
		.S_AXIN_ABORT(1'b0),
		//
		.f_stream_word(fs_word),
		.f_packets_rcvd(fs_packet)
		// }}}
	);

	always @(*)
	if (!i_reset && M_VALID && !i_cfg_reset_fifo)
		assert(M_LAST == (return_len == 0));

	// Verify relationship between r_readptr && rd_wb_addr
	// {{{
	always @(*)
	if (i_reset || rd_outstanding == 0)
		fwb_next_addr = { r_readptr, 2'b00 };
	else begin
		fwb_next_addr = { r_readptr, 2'b00 }
					+ { rd_outstanding, {(WBLSB){1'b0}} };
		if (fwb_next_addr >= end_of_memory)
			fwb_next_addr = fwb_next_addr - wide_memsize;
		fwb_next_addr[1:0] = 2'b00;
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && rd_state != RD_IDLE
				&& rd_state != RD_SIZE && !o_fifo_err)
	begin
		if (rd_state == RD_PACKET || o_wb_stb)
			//	// 8b ptr			// 32b ptr
			assert(fwb_next_addr[AW+WBLSB-1:2] == rd_wb_addr);
	end
	// }}}

	generate if (BUSDW > 32)
	begin : F_WIDE_CHECK
		// The following requires BUSDW > 32 to be expressed
		always @(*)
		if (!i_reset && !i_cfg_reset_fifo && rd_state != RD_IDLE
				&& rd_state != RD_SIZE && !o_fifo_err)
		begin
			//	// 32b ptr			// 32b ptr
			assert(r_readptr[WBLSB-3:0] == rd_wb_addr[WBLSB-3:0]);
		end
	end endgenerate

	// Verify relationship between f_startptr, r_readptr && return_len
	// {{{

	// fwb_bytes_returned: Based upon (r_readptr - f_startptr)
	// {{{
	// These are bytes that have been requested, ackd, and so returned,
	// and may have even been forwarded via M_DATA
	always @(*)
	if (i_reset || rd_state == RD_IDLE || rd_state == RD_SIZE
				// 32b pointer		// 8b pointer
			|| r_readptr[(WBLSB-2)+:AW]==f_startptr[WBLSB +: AW])
	begin
		fwb_bytes_returned = 0;
	end else if (wide_readptr >= f_startptr)
	begin
		fwb_bytes_returned =
			{ wide_readptr[WBLSB +: AW], {(WBLSB){1'b0}} }
				- f_startptr - 4;
	end else begin
		fwb_bytes_returned = wide_memsize
			+ { wide_readptr[WBLSB +: AW], {(WBLSB){1'b0}} }
				- f_startptr - 4;
	end
	// }}}

	// fwb_wide_request : Packet length rounded up to the last word
	// {{{
	always @(*)
	if (i_reset || rd_pktlen == 0)
		fwb_wide_request = 0;
	else begin
		fwb_wide_request = {r_endptr, 2'b00 } - f_startptr;
		fwb_wide_request[WBLSB-1:0] = 0;
		fwb_wide_request = fwb_wide_request + BUSDW/8 - f_startptr[WBLSB-1:0];
	end
	// }}}

	// fwb_bytes_outstanding: rd_outstanding in bytes, Bytes that have
	// {{{
	// been requested, but not ackd.  These bytes are those that haven't
	// yet been returned on the bus.
	always @(*)
	if (rd_outstanding == 0 && !o_wb_stb)
		fwb_bytes_outstanding = 0;
	else if (!full_return)
	begin
		// The number of bytes outstanding is typically given by
		// the number of outstanding requests times the size of the bus.
		// We'll count o_wb_stb as an uncounted request here.
		fwb_bytes_outstanding = { rd_outstanding, {(WBLSB){1'b0}} }
				+ (o_wb_stb ? (BUSDW/8) : 0);

		// The problem is, if !full return, then the first return
		// isn't a request for the full bus width.  So, let's
		// subtract that return back out, and then add back in
		// the number of bytes we expect to get from that first
		// full return.
		fwb_bytes_outstanding = fwb_bytes_outstanding
				- f_startptr[WBLSB-1:0] - 4;
	end else begin
		fwb_bytes_outstanding = { rd_outstanding, {(WBLSB){1'b0}} }
			+ (o_wb_stb ? (BUSDW/8) : 0);
	end
	// }}}

	always @(*)
	begin
		fwb_total = fwb_bytes_returned // + fwb_bytes_outstanding
			+ return_len;
		if (!f_read_aligned && full_return)
			fwb_total = fwb_total - BUSDW/8 + f_startptr[WBLSB-1:0] + 4;
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo
			&& (rd_state == RD_PACKET || rd_state == RD_CLEARBUS)
			&& !o_fifo_err && !dly_check && !dly_fifo_err)
	begin
		assert(fwb_bytes_returned   <= wide_memsize);
		assert(fwb_bytes_outstanding <= wide_memsize);
		assert(fwb_bytes_returned + fwb_bytes_outstanding
						<= wide_memsize);

		assert(fwb_bytes_outstanding <= { f_words_remaining, {(WBLSB){1'b0}} });
		if (return_len > 0)
			assert(fwb_total == rd_pktlen);
	end

	// frd_words: How many words do we need to request to read the entire
	// {{{
	// packet?  Keep in mind, the first word may include the packet length,
	// it may not necessarily be on cut.
	generate if (BUSDW == 32)
	begin : SIMPLE_WORD_LIMIT
		always @(*)
			frd_words = (rd_pktlen + BUSDW/8-1) >> WBLSB;

		assign	f_ptroffset = 0;
	end else begin : OFFCUT_WORD_LIMIT
		always @(*)
		begin
			// How many 32-bit words of the first word need to be
			// read and discarded?  (In bytes)
			frd_words = 0;
			if (!(&f_startptr[WBLSB-1:2]))
				frd_words[WBLSB-1:0] = { f_startptr[WBLSB-1:2], 2'b00} + 4;

			// Now, convert that to our full read size
			frd_words = frd_words + rd_pktlen;
			frd_words = (frd_words + BUSDW/8-1) >> WBLSB;
		end

		assign	f_ptroffset = f_startptr[WBLSB-1:0]+4;

		always @(*)
		if (!i_reset && !o_fifo_err && !i_cfg_reset_fifo)
		case(rd_state)
		RD_IDLE: begin end
		RD_SIZE: begin end
		RD_PACKET: begin
			if (f_ptroffset == 0)
				assert(full_return);
			assert(f_ptroffset == f_read_lsb);
			end
		RD_CLEARBUS: begin
			if (f_ptroffset == 0)
				assert(full_return);
			assert(f_ptroffset == f_read_lsb);
			if (!full_return)
				assert(fwb_bytes_outstanding[WBLSB-1:2] != 0);
			end
		endcase
	end endgenerate
	// }}}

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && !o_fifo_err && rd_state != RD_IDLE
				&& rd_state != RD_SIZE)
	begin
		assert(rd_pktlen >= MINLEN);
		assert(rd_pktlen < MAXLEN);
		assert(fwb_bytes_returned <= frd_words << WBLSB);
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && rd_state == RD_IDLE && !o_fifo_err)
	begin
		assert(!M_VALID || M_LAST || false_ack);
		if (!M_VALID)
			assert(fs_word == 0);
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && rd_state == RD_SIZE)
		assert(fs_word == 0 && !M_VALID);

	always @(*)
		fwb_words_returned = (fwb_bytes_returned + (BUSDW/8)-1)/(BUSDW/8);

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && (rd_state == RD_PACKET
				|| rd_state == RD_CLEARBUS) && !o_fifo_err)
	begin
		assert(fwb_bytes_returned <= (frd_words+1) << WBLSB);
		if (valid_writeptr && return_len > 0)
		begin
			assert((fwb_bytes_returned >> WBLSB) == fs_word
				+ (M_VALID ? 1:0));
		end

		if (!full_return)
			assert(fwb_bytes_returned == 0);
	end
	// }}}

	// Relate rd_outstanding == rd_wb_addr - r_readptr
	// {{{
	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && (rd_state == RD_PACKET
				|| rd_state == RD_CLEARBUS) && !o_fifo_err)
	begin
		if (rd_wb_addr >= r_readptr)
		begin
			assert((rd_outstanding == rd_wb_addr[(WBLSB-2)+:AW]
					- r_readptr[(WBLSB-2)+:AW])
				|| ({ rd_outstanding, {(WBLSB){1'b0}} } == wide_memsize));
		end else begin
			assert(rd_outstanding == wide_memsize[WBLSB+:AW]
				+rd_wb_addr[(WBLSB-2)+:AW]
					- r_readptr[(WBLSB-2)+:AW]);
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stream counting
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (!i_reset && !full_return && rd_state != RD_IDLE
						&& rd_state != RD_SIZE)
		assert(return_len == rd_pktlen);

	always @(*)
	if (!full_return)
	begin
		f_words_remaining = return_len + 4;
		f_words_remaining = f_words_remaining + f_startptr[WBLSB-1:0];
		// Now, round up to the nearest word
		f_words_remaining = f_words_remaining + (BUSDW/8-1);
		f_words_remaining = f_words_remaining >> WBLSB;
	end else if (f_read_aligned)
		f_words_remaining = (return_len + (BUSDW/8-1)) >> WBLSB;
	else begin
		f_words_remaining = return_len + (BUSDW/8)-1;
		f_words_remaining = f_words_remaining
				- (BUSDW/8 - f_read_lsb);
		f_words_remaining = f_words_remaining >> WBLSB;
	end

	always @(*)
	if (!i_reset && !o_fifo_err && !i_cfg_reset_fifo) case(rd_state)
	RD_IDLE: begin end
	RD_SIZE: begin
		assert(fwb_addr[WBLSB +: AW] == r_readptr[WBLSB-2 +: AW]);
		end
	RD_PACKET: begin
		if (full_return && wide_readptr[WBLSB-1:0] != 0)
		begin
			assert(return_len + fwb_bytes_returned
				- ((BUSDW/8) - wide_readptr[WBLSB-1:0])
				== rd_pktlen);
		end else begin
			assert(full_return || return_len == rd_pktlen);
			assert(full_return || fwb_bytes_returned == 0);
		end

		if (valid_writeptr)
		begin
			assert((rd_pktlen - fwb_bytes_returned)
				<= { f_words_remaining, {(WBLSB){1'b0}} });
		end

		if (o_wb_stb)
		begin
			if (full_return)
			begin
				assert(fwb_bytes_returned
					+ fwb_bytes_outstanding
					- (BUSDW/8) < f_pktlen);
			end
		end else begin
			assert(fwb_bytes_returned + fwb_bytes_outstanding < f_pktlen);
		end
		// *****
		if (f_startptr[WBLSB +: AW] <= r_readptr[WBLSB-2+: AW])
		begin
			assert(f_startptr <= wide_readptr);
		end else begin
			assert(f_startptr <= wide_memsize + wide_readptr);
		end
		assert(dly_check || dly_fifo_err
			|| wide_end_of_packet[WBLSB +: AW] != f_startptr[WBLSB +: AW]);
		if (f_startptr < wide_end_of_packet)
		begin
			// No memory wrapping
			assert(dly_check || dly_fifo_err
				|| fwb_addr < wide_end_of_packet);
			if (dly_check)
			begin
			end else if (BUSDW <= 64)
				assert(f_startptr <= fwb_addr);
			else begin
				assert({f_startptr[WBLSB +: AW], {(WBLSB){1'b0}} } <= fwb_addr);
			end
			assert(f_startptr < wide_readptr);
		end else if (f_startptr[WBLSB +: AW] <= o_wb_addr)
		begin
			// end_of_packet < Start < fwb_addr < end_of_memory
			assert(f_startptr < wide_readptr);
			assert(fwb_addr < end_of_memory);
			assert(o_wb_addr == wide_readptr[WBLSB +: AW] + rd_outstanding);
			assert(dly_check || dly_fifo_err || wide_end_of_packet < f_startptr);
		end else if (f_startptr < wide_readptr)
		begin
			// fwb_addr < start < readptr < end_of_memory
			assert(dly_check || fwb_addr < wide_end_of_packet);
			assert(o_wb_addr == wide_readptr[WBLSB +: AW]
				+ rd_outstanding - i_cfg_memsize);
			assert(wide_end_of_packet < f_startptr);
		end else begin
			// readptr < fwb_addr < start
			assert(dly_check || dly_fifo_err
				|| wide_end_of_packet < f_startptr);
			assert((r_readptr >> (WBLSB-2)) <= o_wb_addr);
			assert(dly_fifo_err
				|| wide_readptr[WBLSB +: AW] < f_startptr[WBLSB +: AW]);
			assert(dly_check || dly_fifo_err
				|| fwb_addr < wide_end_of_packet);
		end
		// *****
		assert({ r_readptr, 2'b00 } != f_startptr);
		assert(return_len > 0);
		assert(fwb_bytes_returned[1:0] == 2'b00);
		if (BUSDW == 32 || full_return)
		begin
			assert(fwb_bytes_outstanding
				<= { f_words_remaining, {(WBLSB){1'b0}} });
		end else if (o_wb_stb || rd_outstanding > 0)
		begin
			// assert(fwb_bytes_outstanding[WBLSB-1:2] != 0);
			assert(return_len == rd_pktlen);
			assert(fwb_bytes_returned == 0);
			assert(fwb_bytes_outstanding[WBLSB+AW-1:WBLSB] + 1
					<= f_words_remaining);
		end end
	RD_CLEARBUS: begin
		// ***
		// assert(f_startptr <= wide_readptr);
		// ***
		assert(wide_end_of_packet[WBLSB +: AW] != f_startptr[WBLSB +: AW]);
		if (f_startptr < wide_end_of_packet)
		begin
			if (o_wb_stb || rd_outstanding > 0)
			begin
				assert(f_startptr < wide_readptr);
			end

			if (o_wb_stb)
			begin
				assert(wide_readptr[WBLSB +: AW] <= fwb_addr);
				assert(fwb_addr[WBLSB +: AW] <= wide_end_of_packet[WBLSB +: AW]);
			end

			if (!o_wb_stb && wide_readptr < f_startptr)
			begin
				assert(wide_readptr[WBLSB +: AW] == wide_baseaddr[WBLSB +: AW]);
				assert(rd_outstanding == 0);
			end
		end else if (wide_readptr < f_startptr)
		begin
			assert(return_len == 0 || wide_readptr[WBLSB +: AW] != f_startptr[WBLSB +: AW]);
			assert((r_readptr >> (WBLSB-2)) <= o_wb_addr);
			assert(wide_end_of_packet < f_startptr);
			if (o_wb_stb)
			begin
				assert(fwb_addr < f_startptr);
			end
		end else
			assert(r_readptr >= f_startptr[2 +: (AW+WBLSB-2)]+1);
		assert({ r_readptr, 2'b00 } != f_startptr);
		if (full_return)
		begin
			assert(!o_wb_stb || o_wb_addr == f_endptr[WBLSB +: AW]);
		end
		if (o_wb_stb || rd_outstanding > 0)
			assert(fwb_bytes_returned[1:0] == 2'b00);
		assert(fwb_bytes_outstanding + fwb_bytes_returned
			<= rd_pktlen + (BUSDW/8)-1);
		assert(return_len == 0
			|| fwb_bytes_outstanding + fwb_bytes_returned >= rd_pktlen);
		if (BUSDW == 32 || full_return)
		begin
			assert(fwb_bytes_outstanding
				== { f_words_remaining, {(WBLSB){1'b0}} });
		end else begin
			assert(fwb_bytes_outstanding[WBLSB+AW-1:WBLSB] + 1
					== f_words_remaining);
		end end
	endcase

	/*
	wire	[AW+WBLSB:0]	f_overread;

	generate if (BUSDW > 32)
	begin
		reg	[AW+WBLSB:0]	fr_overread;

		always @(*)
		begin
			// First, how many bytes do we need to read total?
			fr_overread = rd_pktlen;
			if (!(&f_startptr[WBLSB-1:2]))// && !full_return)
				fr_overread = fr_overread + f_startptr[WBLSB-1:0] + 4;
			// fr_overread = fr_overread + 3;
			// fr_overread[1:0] = 2'b00;
			// Get the remainder, modulo one word
			fr_overread[AW+WBLSB:WBLSB] = 0;

			// If this isn't zero, we'll be reading more than
			// desired.  How much more is the difference.
			if (fr_overread != 0)
				fr_overread = (BUSDW/8)-fr_overread;
		end

		assign	f_overread = fr_overread;

	end else begin
		assign	f_overread = 0;
	end endgenerate
	*/

	generate if (BUSDW>32)
	begin : F_WIDE
		always @(*)
		if (!i_reset && rd_state != RD_IDLE && rd_state != RD_SIZE
				&& valid_writeptr && !i_cfg_reset_fifo
				&& !o_fifo_err)
		begin
			if (!full_return)
			begin
				assert(!(&f_startptr[WBLSB-1:2]));
			end else if (return_len > 0)
			begin
				assert(&f_startptr[WBLSB-1:2]
					|| fwb_bytes_returned>0);
			end
		end
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// (* anyconst *) reg	[AW+WBLSB-1:0]	fc_posn;
	// (* anyconst *) reg	[7:0]		fc_byte;
	//	reg	[BUSDW-1:0]	f_byte_wide;

	// Pick a byte position within a packet.
	// always @(*)
	// if (rd_state == RD_PACKET || rd_state == RD_CLEARBUS)
	//	assume(fc_posn < rd_pktlen);
	//

	// Pick a value to be at that byte.
	// Assume that value gets returned, when i_wb_ack is high
	// {{{

	// ... ??
	// bus_byte =
	// always @(*)
	// if (!i_reset && o_wb_cyc && i_wb_ack &&
	//	assume(bus_byte == fc_byte);
	// }}}

	// *PROVE* that value is set in M_DATA when the byte is sent.
	// {{{
	// generate if (OPT_LITTLE_ENDIAN)
	// begin
	//
	//	always @(*)
	//		f_byte_wide = M_DATA >> (fc_posn[WBLSB-1:0] * 8);
	//	assign	f_byte = f_byte_wide[7:0];
	//
	// end else begin
	//	always @(*)
	//		f_byte_wide = M_DATA << (fc_posn[WBLSB-1:0] * 8);
	//	assign	f_byte = f_byte_wide[BUSDW-8 +: 8];
	// end endgenerate

	// always @(*)
	// if (!i_reset && M_VALID && { fs_word, {(WBLSB){1'b0}} } <= fc_posn
	//		&& fc_posn < { fs_word, {(WBLSB){1'b0}} })
	//	assert(f_byte == fc_byte);
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[3:0]	cvr_packets;

	initial	cvr_packets <= 0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || o_fifo_err)
		cvr_packets <= 0;
	else if (!cvr_packets[3] && M_VALID && M_LAST)
		cvr_packets <= cvr_packets + 1;

	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo && !o_fifo_err)
	begin
		cover(cvr_packets == 1);
		cover(cvr_packets == 2);
		cover(cvr_packets == 3);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)	assume(fc_baseaddr == 0);
	always @(*)	assume($countones(fc_memsize)==1);
	// always @(*)	assume(fc_memsize == { 1'b1, {(AW-1){1'b0}} });
	// always @(*) if (rd_state == RD_SIZE) assume(next_rdlen == 128+4);

	/*
	always @(*)
	if (!i_reset && rd_state != RD_IDLE && rd_state != RD_SIZE
				// 32b pointer		// 8b pointer
			&& r_readptr[(WBLSB-2)+:AW]!=f_startptr[WBLSB +: AW])
	begin
		// Prevent memory wrapping?
		assume(r_readptr[(WBLSB-2)+: AW] >= f_startptr[WBLSB +: AW]);
	end

	always @(*)
	if (!i_reset && rd_state != RD_IDLE && rd_state != RD_SIZE)
	begin
		assume(f_startptr + rd_pktlen + 8 + BUSDW/8
						< fc_baseaddr + fc_memsize);
	end
	*/

	// }}}
`endif
// }}}
endmodule
