////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/pktvfifo.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A virtual packet FIFO.  Fundamentally, this core acts as a
//		FIFO for packets.
//
//	"Virual" means that the FIFO memory is external to the board, and
//		likely kept in an SDRAM RAM, such as a DDR3 SDRAM.  It will be
//		accessed via a Wishbone bus.
//
//	"Packet" means two things: First, the data are separated into packets,
//		each packet having a beginning and an end and some (as yet
//		unspecified) number of bytes within it.  Second, any failure
//		in the receive processing chain, such as a buffer overflow
//		while waiting for the bus or a CRC error, the  and the
//		"packet" will need to be dropped in its entirety.  This needs
//		to include dropping the packet if we run out of memory before
//		the packet completes as well.
//
//	In general, the VFIFO operates in the following manner:
//
//	1. First, a conversion takes place from the packet data width to the
//		bus data width.  Since our design is intended to process
//		packets at 32-bits per 312.5 clock cycle, and then cross from
//		there to the memory clock, we'll need to be at least 64-bits
//		per clock--possibly more.  The memory, however, has been sized
//		to 512bits per clock.  This should be sufficient to keep up
//		with four diverse ports both reading and writing memory at the
//		same time.
//	2. The result goes into an (optional) small FIFO.  Normally I'd wait
//		for this FIFO to get at least half full before writing, but my
//		netfifo currently doesn't report on how much data it has
//		within it.  Therefore, we'll initiate a write beat whenever the
//		FIFO is non-empty.
//	3. From there, a state machine writes packets to memory.
//		A. Prior to any packet in memory is a 32-bit length word.
//		B. This word is initially set to zero, while no packet is
//			present.
//		C. As packet data is written to memory, this word is preserved.
//		D. If an ABORT happens before the memory is written, the write
//			pointer simply goes back to the zero length word.
//		D. Once the packet is complete, it can be *committed* to memory.
//			This takes two steps.  First, the next 32-bit length
//			word is set to zero.
//		E. Then the state machine goes back and writes the (now known)
//			32'bit length word at the beginning of the packet.
//		F. The state machine is then ready for the next packet.
//	4. As packets are committed, once the last ACK is received, a packet
//		counter is incremented to tell the read state machine it can
//		start reading a packet.
//	5. A separate state machine now reads from memory, once a packet has
//		been fully committed to it.
//		A. It first reads the 32-bit length word.
//		B. Then it reads data from memory
//		C. Beware, this memory is 32-bit aligned, but not necessarily
//			bus width aligned.
//	6. The data is then pushed into another small FIFO.
//	7. To keep logic down, we drop back down from the bus width to the
//		width of a packet.
//
//	At least, that's how things are *supposed* to happen.
//
// Registers:
//	0: The base address in memory.  Must point to a valid address to which
//		packets may be written.  This address, a full octet address,
//		must be bus aligned.  To know the appropriate bus alignment,
//		you can write a -1 to this field and then read it back.  The
//		resulting value will a valid bus aligned address--not a very
//		useful one, but a valid one.
//
//		This FIFO has been designed to operate without CPU
//		intervention.  To do so, the DEF_BASEADDR may be set to a
//		default base address of a fixed memory allocation.  This
//		allocation may be adjusted by the CPU later.
//	4. The size of memory allocated to this FIFO.  Must be greater than
//		zero for the FIFO to come out of reset.  May be equal to the
//		entire size of memory, but there must be enough room for this
//		much memory between the base address and the end of memory
//		in order for the FIFO to come out of reset.
//
//		This FIFO has been designed to operate without CPU
//		intervention.  To do so, DEF_MEMSIZE may be set to a default
//		memory size.  If this size is non-zero, the FIFO will come out
//		of reset on its own.
//	8. The write pointer, pointing to the length word of the next packet
//		to be committed to the FIFO.  This isn't really all that
//		valuable to the CPU, but looking for changes in this value can
//		be an indication of the FIFO getting used.
//	12. The read pointer, pointing to one past the last 32-bit word read
//		from memory (i.e. the next word to be read from memory).  If
//		this pointer == the write pointer, then the memory is understood
//		to be empty.
//
//	There is currently no external indication that the FIFO is not in
//	working order.  (There probably should be ...)
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
`timescale 1ns/1ps
`default_nettype none
// }}}
module	pktvfifo #(
		// {{{
		parameter	PKTDW = 64,
		parameter	PKTBYW = $clog2(PKTDW/8),
		parameter	BUSDW = 512,
		parameter	AW = 30-$clog2(BUSDW/8),
		parameter [AW-1:0] DEF_BASEADDR = {(AW){1'b0}},
		parameter [AW-1:0] DEF_MEMSIZE  = {(AW){1'b0}},
		parameter	LGPIPE = 6,
		parameter	LGFIFO = 5,
		parameter [0:0]	OPT_LOWPOWER = 1,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 0
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_reset,
		input	wire		i_net_reset,
		// WB Control port
		// {{{
		input	wire		i_ctrl_cyc, i_ctrl_stb, i_ctrl_we,
		input	wire	[2:0]	i_ctrl_addr,
		input	wire	[31:0]	i_ctrl_data,
		input	wire	[3:0]	i_ctrl_sel,
		output	wire		o_ctrl_stall,
		output	reg		o_ctrl_ack,
		output	reg	[31:0]	o_ctrl_data,
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
		output	reg			M_ABORT
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	// Local parameters
	// {{{
	localparam	WBLSB = $clog2(BUSDW/8);

	localparam	[2:0]	ADR_BASEADDR = 3'b000,
				ADR_SIZE     = 3'b001,
				ADR_WRITEPTR = 3'b010,
				ADR_READPTR  = 3'b011,
				ADR_PKTCOUNT = 3'b100,
				ADR_BYTECOUNT= 3'b101,
				ADR_FIFOPKTS = 3'b110,
				ADR_FIFOBYTES= 3'b111;
	// }}}

	reg	[AW-1:0]	r_baseaddr,
				r_memsize;
	reg	[31:0]		new_baseaddr;
	reg	[31:0]		new_memsize;

	reg	[26:0]	txpkt_count;
	reg	[32:0]	txbyte_count;
	reg	[31:0]	w_tx_debug, w_rx_debug, pkts_in_fifo, bytes_in_fifo;
	reg		r_dbg_vfifo, mid_txpkt;


	wire	[AW+(WBLSB-2)-1:0]	w_writeptr, w_readptr;

	reg			reset_fifo, mem_err;
	wire			ign_outw_abort;

	wire				ipkt_valid, ipkt_ready,
					ipkt_last, ipkt_abort;
	wire	[BUSDW-1:0]		ipkt_data;
	wire	[$clog2(BUSDW/8):0]	ipkt_bytes;

	wire				wide_valid, wide_ready,
					wide_last, wide_abort;
	wire	[BUSDW-1:0]		wide_data;
	wire	[$clog2(BUSDW/8)-1:0]	wide_bytes;

	wire			wr_wb_cyc, wr_wb_stb, wr_wb_we;
	wire	[AW-1:0]	wr_wb_addr;
	wire	[BUSDW-1:0]	wr_wb_data, wr_wb_idata;
	wire	[BUSDW/8-1:0]	wr_wb_sel;
	wire			wr_wb_stall, wr_wb_ack, wr_wb_err;

	wire			rd_wb_cyc, rd_wb_stb, rd_wb_we;
	wire	[AW-1:0]	rd_wb_addr;
	wire	[BUSDW-1:0]	rd_wb_data, rd_wb_idata;
	wire	[BUSDW/8-1:0]	rd_wb_sel;
	wire			rd_wb_stall, rd_wb_ack, rd_wb_err;

	wire	ctrl_write;


	wire				ack_valid, ack_last;
	wire	[BUSDW-1:0]		ack_data;
	wire [$clog2(BUSDW/8)-1:0]	ack_bytes;
	wire				ackfifo_read, ackfifo_rd;

	wire			ign_ackfifo_full, ackfifo_empty, ackfifo_last;
	wire	[LGFIFO:0]	ign_ackfifo_fill;
	wire	[BUSDW-1:0]	ackfifo_data;
	wire	[$clog2(BUSDW/8)-1:0]	ackfifo_bytes;

	wire	msb_bytes;

	assign	ctrl_write = i_ctrl_stb && i_ctrl_we && (&i_ctrl_sel) && !o_ctrl_stall;
	wire	rd_fifo_err;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Control logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// reset_fifo
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_net_reset)
		reset_fifo <= 0;
	else if ((o_wb_cyc && i_wb_err) || (rd_fifo_err) || mem_err)
		reset_fifo <= 1;
	else if (ctrl_write && (i_ctrl_addr == ADR_BASEADDR
					|| i_ctrl_addr == ADR_SIZE))
		reset_fifo <= 1;
	else if ((r_memsize == 0) || (r_baseaddr + r_memsize > (1<<AW)))
		reset_fifo <= 1;
	else if (!M_VALID || M_READY)
		reset_fifo <= mem_err;
	// }}}

	// mem_err
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_net_reset)
		mem_err <= 0;
	else if (o_wb_cyc && i_wb_err)
		mem_err <= 1;
	else if (ctrl_write && (i_ctrl_addr == ADR_BASEADDR
					|| i_ctrl_addr == ADR_SIZE))
		mem_err <= 0;
	// }}}

	// r_baseaddr
	// {{{
	always @(*)
	begin
		new_baseaddr = 0;
		new_baseaddr[WBLSB +: AW] = r_baseaddr;
		if (i_ctrl_sel[0])
			new_baseaddr[ 7: 0] = i_ctrl_data[ 7: 0];
		if (i_ctrl_sel[1])
			new_baseaddr[15: 8] = i_ctrl_data[15: 8];
		if (i_ctrl_sel[2])
			new_baseaddr[23:16] = i_ctrl_data[23:16];
		if (i_ctrl_sel[3])
			new_baseaddr[31:24] = i_ctrl_data[31:24];

		new_baseaddr[WBLSB-1:0] = 0;
		new_baseaddr[31:AW+WBLSB] = 0;
	end

	always @(posedge i_clk)
	if (i_reset)
		r_baseaddr <= DEF_BASEADDR;
	else if (ctrl_write && i_ctrl_addr == ADR_BASEADDR)
	begin
		r_baseaddr <= new_baseaddr[WBLSB +: AW];
	end
	// }}}

	// r_memsize
	// {{{
	always @(*)
	begin
		new_memsize = 0;
		new_memsize[WBLSB +: AW] = r_memsize;

		if (i_ctrl_sel[0])
			new_memsize[ 7: 0] = i_ctrl_data[ 7: 0];
		if (i_ctrl_sel[1])
			new_memsize[15: 8] = i_ctrl_data[15: 8];
		if (i_ctrl_sel[2])
			new_memsize[23:16] = i_ctrl_data[23:16];
		if (i_ctrl_sel[3])
			new_memsize[31:24] = i_ctrl_data[31:24];

		new_memsize[WBLSB-1:0] = 0;
		new_memsize[31:AW+WBLSB]   = 0;
	end

	always @(posedge i_clk)
	if (i_reset)
		r_memsize <= DEF_MEMSIZE;
	else if (ctrl_write && i_ctrl_addr == ADR_SIZE)
		r_memsize <= new_memsize[WBLSB +: AW];
	// }}}

	assign	o_ctrl_stall = 0;
	always @(posedge i_clk)
	if (i_reset || !i_ctrl_cyc)
		o_ctrl_ack <= 0;
	else
		o_ctrl_ack <= i_ctrl_stb;

	// r_dbg_vfifo
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		r_dbg_vfifo <= 1'b0;
	else if (ctrl_write && i_ctrl_addr == ADR_PKTCOUNT)
		r_dbg_vfifo <= i_ctrl_data[31];
	// }}}

	// o_ctrl_data
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && (i_reset || !i_ctrl_stb || i_ctrl_we))
		o_ctrl_data <= 0;
	else begin
		o_ctrl_data <= 0;
		case(i_ctrl_addr)
		ADR_BASEADDR:	o_ctrl_data[WBLSB +: AW] <= r_baseaddr;
		ADR_SIZE:	if (!i_net_reset)
					o_ctrl_data[WBLSB +: AW] <= r_memsize;
		ADR_WRITEPTR:	if (!i_net_reset)
					o_ctrl_data[AW+WBLSB-1:2] <= w_writeptr;
		ADR_READPTR:	if (!i_net_reset)
					o_ctrl_data[AW+WBLSB-1:2] <= w_readptr;
		ADR_PKTCOUNT: if (r_dbg_vfifo)
				o_ctrl_data <= w_tx_debug;
			else if (txpkt_count[26])
				o_ctrl_data <= 32'hffff_ffff;
			else
				o_ctrl_data[25:0] <= txpkt_count[25:0];
		ADR_BYTECOUNT: if (r_dbg_vfifo)
				o_ctrl_data <= w_rx_debug;
			else if (txbyte_count[32])
				o_ctrl_data <= 32'hffff_ffff;
			else
				o_ctrl_data <= txbyte_count[31:0];
		ADR_FIFOPKTS:
			o_ctrl_data <= pkts_in_fifo;
		ADR_FIFOBYTES:
			o_ctrl_data <= bytes_in_fifo;
		endcase
	end

	always @(posedge i_clk)
	if (i_reset || i_net_reset)
		txpkt_count <= 0;
	else if (M_VALID && M_READY && M_LAST && !txpkt_count[26])
		txpkt_count <= txpkt_count + 1;

	always @(posedge i_clk)
	if (i_reset || i_net_reset)
		txbyte_count <= 0;
	else if (M_VALID && M_READY && !txbyte_count[32])
		txbyte_count <= txbyte_count + { {(32-PKTBYW){1'b0}},
							msb_bytes, M_BYTES };

	always @(posedge i_clk)
	if (i_reset || i_net_reset)
		mid_txpkt <= 1'b0;
	else if (M_ABORT && (!M_VALID || M_READY))
		mid_txpkt <= 1'b0;
	else if (M_VALID && M_READY)
		mid_txpkt <= !M_LAST;

	always @(posedge i_clk)
	if (i_reset || i_net_reset || reset_fifo)
		pkts_in_fifo <= 0;
	else case({ (S_VALID && S_READY && S_LAST),
				(M_VALID && M_READY && M_LAST)})
	2'b01: pkts_in_fifo <= pkts_in_fifo - 1;
	2'b10: pkts_in_fifo <= pkts_in_fifo + 1;
	default: begin end
	endcase

	always @(posedge i_clk)
	if (i_reset || i_net_reset || reset_fifo)
		bytes_in_fifo <= 0;
	else case({ (S_VALID && S_READY), (M_VALID && M_READY)})
	2'b00: begin end
	2'b01: bytes_in_fifo <= bytes_in_fifo
			- { {(31-PKTBYW){1'b0}}, msb_bytes, M_BYTES };
	2'b10: bytes_in_fifo <= bytes_in_fifo
			+ { {(31-PKTBYW){1'b0}}, (S_BYTES==0), S_BYTES };
	2'b11: bytes_in_fifo <= bytes_in_fifo
			+ { {(31-PKTBYW){1'b0}}, (S_BYTES==0), S_BYTES }
			- { {(31-PKTBYW){1'b0}}, msb_bytes, M_BYTES };
	endcase

	always @(*)
	begin
		w_tx_debug = {
			(vfifo_rd.return_len[AW+WBLSB-1:20] != 0) ? 20'hfffff
				: vfifo_rd.return_len[19:0],
			vfifo_rd.rd_state[1:0], rd_wb_cyc, rd_wb_stb,	// 4b
			mid_txpkt, vfifo_rd.rd_outstanding[LGPIPE:0] };		// 8b

		w_rx_debug = {
			(vfifo_wr.wr_pktlen[AW+WBLSB-1:20] != 0) ? 20'hfffff
				: vfifo_wr.wr_pktlen[19:0],
			vfifo_wr.wr_state[2:0], wr_wb_cyc,		// 4b
			wr_wb_stb, vfifo_wr.wr_outstanding[LGPIPE:0] };		// 8b
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming width adjustment
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axinwidth #(
		.IW(PKTDW), .OW(BUSDW), .OPT_LITTLE_ENDIAN(1'b0)
	) u_inwidth (
		// {{{
		.ACLK(i_clk), .ARESETN(!i_reset && !reset_fifo && !i_net_reset),
		//
		.S_AXIN_VALID(S_VALID),
		.S_AXIN_READY(S_READY),
		.S_AXIN_DATA( S_DATA),
		.S_AXIN_BYTES({ (S_BYTES[$clog2(PKTDW/8)-1:0] == 0),
					S_BYTES[$clog2(PKTDW/8)-1:0] }),
		.S_AXIN_LAST( S_LAST),
		.S_AXIN_ABORT(S_ABORT),
		//
		.M_AXIN_VALID(ipkt_valid),
		.M_AXIN_READY(ipkt_ready),
		.M_AXIN_DATA( ipkt_data),
		.M_AXIN_BYTES(ipkt_bytes),
		.M_AXIN_LAST( ipkt_last),
		.M_AXIN_ABORT(ipkt_abort)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming data FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (LGFIFO > 1)
	begin : GEN_NETFIFO
		netfifo #(
			.BW(BUSDW + WBLSB), .LGFLEN(LGFIFO)
		) u_prefifo (
			// {{{
			.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset && !i_net_reset),
			//
			.S_AXIN_VALID(ipkt_valid),
			.S_AXIN_READY(ipkt_ready),
			.S_AXIN_DATA({ ipkt_bytes[$clog2(BUSDW/8)-1:0],
							ipkt_data }),
			.S_AXIN_LAST( ipkt_last),
			.S_AXIN_ABORT(ipkt_abort),
			//
			.M_AXIN_VALID(wide_valid),
			.M_AXIN_READY(wide_ready),
			.M_AXIN_DATA({ wide_bytes, wide_data }),
			.M_AXIN_LAST( wide_last),
			.M_AXIN_ABORT(wide_abort)
			// }}}
		);
	end else begin : NO_NETFIFO
		assign	wide_valid = ipkt_valid;
		assign	ipkt_ready = wide_valid;
		assign	wide_data  = ipkt_data;
		assign	wide_bytes = ipkt_bytes;
		assign	wide_last  = ipkt_last;
		assign	wide_abort = ipkt_abort;
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write incoming packets to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	pktvfifowr #(
		// {{{
		.AW(AW), .BUSDW(BUSDW), .LGPIPE(LGPIPE),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN)
		// }}}
	) vfifo_wr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || i_net_reset),
		//
		.i_cfg_reset_fifo(reset_fifo), .i_cfg_mem_err(mem_err),
		.i_cfg_baseaddr(r_baseaddr), .i_cfg_memsize(r_memsize),
		.i_readptr(w_readptr), // .i_mempkts(mempkts),
		.o_writeptr(w_writeptr), // .o_pktwr_stb(pktwr_stb),
		//
		.S_VALID(wide_valid), .S_READY(wide_ready),
		.S_DATA(wide_data), .S_BYTES(wide_bytes),
		.S_LAST(wide_last), .S_ABORT(wide_abort),
		//
		.o_wb_cyc( wr_wb_cyc),  .o_wb_stb(  wr_wb_stb),
		.o_wb_we(  wr_wb_we),
		.o_wb_addr(wr_wb_addr), .o_wb_data( wr_wb_data),
		.o_wb_sel( wr_wb_sel),  .i_wb_stall(wr_wb_stall),
		.i_wb_ack( wr_wb_ack),  // .i_wb_data( wr_wb_idata),
		.i_wb_err( wr_wb_err)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Count available packets in memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Not needed.  Now doing (readptr != writeptr) to tell us if packets
	// are available.

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read packets back out from memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	pktvfiford #(
		// {{{
		.AW(AW), .BUSDW(BUSDW), .LGPIPE(LGPIPE),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN)
		// }}}
	) vfifo_rd (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || i_net_reset),
		//
		.i_cfg_reset_fifo(reset_fifo), // .i_cfg_mem_err(mem_err),
		.i_cfg_baseaddr(r_baseaddr), .i_cfg_memsize(r_memsize),
		.i_writeptr(w_writeptr), .o_readptr(w_readptr),
		.o_fifo_err(rd_fifo_err),
		//
		.o_wb_cyc( rd_wb_cyc),  .o_wb_stb(  rd_wb_stb),
		.o_wb_we(  rd_wb_we),
		.o_wb_addr(rd_wb_addr), .o_wb_data( rd_wb_data),
		.o_wb_sel( rd_wb_sel),  .i_wb_stall(rd_wb_stall),
		.i_wb_ack( rd_wb_ack),  .i_wb_data( rd_wb_idata),
		.i_wb_err( rd_wb_err),
		//
		.M_VALID(ack_valid), // .M_READY(ack_ready),
		.M_DATA(ack_data), .M_BYTES(ack_bytes),
		.M_LAST(ack_last), // .M_ABORT(ack_abort)
		.i_fifo_rd(ackfifo_rd)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Arbitrate between the two packet handlers
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbmarbiter #(
		.DW(BUSDW), .AW(AW), .NIN(2), .LGFIFO(LGFIFO)
	) u_bus_arbiter (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || i_net_reset),
		//
		.s_cyc( { wr_wb_cyc,    rd_wb_cyc }),
		.s_stb( { wr_wb_stb,    rd_wb_stb }),
		.s_we(  { wr_wb_we,	rd_wb_we  }),
		.s_addr({ wr_wb_addr,   rd_wb_addr }),
		.s_data({(2){wr_wb_data}}),
		.s_sel( { wr_wb_sel,    rd_wb_sel }),
		.s_stall({ wr_wb_stall, rd_wb_stall }),
		.s_ack(  { wr_wb_ack,   rd_wb_ack }),
		.s_idata({ wr_wb_idata, rd_wb_idata }),
		.s_err({   wr_wb_err,   rd_wb_err }),
		//
		.m_cyc(  o_wb_cyc ),
		.m_stb(  o_wb_stb ),
		.m_we(   o_wb_we  ),
		.m_addr( o_wb_addr),
		.m_data( o_wb_data),
		.m_sel(  o_wb_sel ),
		.m_stall(i_wb_stall),
		.m_ack(  i_wb_ack),
		.m_idata(i_wb_data),
		.m_err(  i_wb_err)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Return data FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// We can't skip on the ACK FIFO.  We need it to handle backpressure.
	// The FIFO helps us guarantee that we don't overload this in back
	// pressure.
	sfifo #(
		.BW(BUSDW + $clog2(BUSDW/8) + 1), .LGFLEN(LGFIFO)
	) u_ackfifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || i_net_reset),
		.i_wr(ack_valid), .i_data({ ack_last, ack_bytes, ack_data }),
			.o_full(ign_ackfifo_full), .o_fill(ign_ackfifo_fill),
		.i_rd(ackfifo_rd),
			.o_data({ ackfifo_last, ackfifo_bytes, ackfifo_data }),
			.o_empty(ackfifo_empty)
		// }}}
	);

	assign	ackfifo_rd = ackfifo_read && !ackfifo_empty;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing width adjustment
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (i_reset || i_net_reset)
		M_ABORT <= 1'b0;
	else if (reset_fifo)
		M_ABORT <= 1'b1;
	else if (!M_VALID || M_READY)
		M_ABORT <= 1'b0;

	axinwidth #(
		.IW(BUSDW), .OW(PKTDW), .OPT_LITTLE_ENDIAN(1'b0)
	) u_outwidth (
		// {{{
		.ACLK(i_clk), .ARESETN(!i_reset && !reset_fifo && !i_net_reset),
		//
		.S_AXIN_VALID(!ackfifo_empty),
		.S_AXIN_READY(ackfifo_read),
		.S_AXIN_DATA(ackfifo_data),
		.S_AXIN_BYTES({ (ackfifo_bytes== 0), ackfifo_bytes }),
		.S_AXIN_LAST(ackfifo_last),
		.S_AXIN_ABORT(1'b0),
		//
		.M_AXIN_VALID(M_VALID),
		.M_AXIN_READY(M_READY),
		.M_AXIN_DATA(M_DATA),
		.M_AXIN_BYTES({ msb_bytes, M_BYTES }),
		.M_AXIN_LAST(M_LAST),
		.M_AXIN_ABORT(ign_outw_abort)
		// }}}
	);

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, new_memsize, new_baseaddr,
				ipkt_bytes[$clog2(BUSDW/8)],
				ign_ackfifo_full, ign_ackfifo_fill,
				wr_wb_idata, ign_outw_abort, rd_wb_data };
	// Verilator lint_on  UNUSED
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
`endif
// }}}
endmodule
