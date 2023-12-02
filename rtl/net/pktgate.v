////////////////////////////////////////////////////////////////////////////////
//
// Filename:	pktgate.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	The packet gate has a simple purpose: buffer a whole packet,
//		and don't release that packet until either 1) an entire packet
//	has been buffered, or 2) the buffer has filled up.  This is to help
//	guarantee that once we start transmitting a packet (the next step),
//	that the packet will be able to complete its transmission without
//	any cycles where !M_AXIN_VALID between the first VALID and LAST.
//
//	The below logic should look very much like the netfifo.v module.
//	with a few exceptions:
//
//	output_active is the register used to represent this gating feature.
//	Packets will only get forwarded if output_active is true.
//
//	The buffer will only run dry on a packet if the packet first filled
//	the buffer, and then had to be switched to coming from the input.
//	In this case, the input must have been in the middle of a packet when
//	the buffer ran dry, and the rest of the incoming packet must now be
//	aborted.  Capturing this condition is the purpose of the abort_input
//	signal below.
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
`default_nettype none
// }}}
module	pktgate #(
		// {{{
		parameter	DW=16,	// Byte/data width
		parameter 	LGFLEN=4,
		parameter [0:0]	OPT_ASYNC_READ = 1'b1,
		parameter [0:0]	OPT_WRITE_ON_FULL = 1'b0,
		parameter [0:0]	OPT_READ_ON_EMPTY = 1'b0,
		localparam	FLEN=(1<<LGFLEN)
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,
		input	wire		S_AXI_ARESETN,
		//
		// Write interface
		input	wire			S_AXIN_VALID,
		output	reg			S_AXIN_READY,
		input	wire [DW-1:0]		S_AXIN_DATA,
		input	wire [$clog2(DW/8)-1:0]	S_AXIN_BYTES,
		input	wire			S_AXIN_LAST,
		input	wire			S_AXIN_ABORT,
		//
		// Read interface
		output	wire			M_AXIN_VALID,
		input	wire			M_AXIN_READY,
		output	wire [DW-1:0]		M_AXIN_DATA,
		output	wire [$clog2(DW/8)-1:0]	M_AXIN_BYTES,
		output	wire			M_AXIN_LAST,
		output	reg			M_AXIN_ABORT
		// }}}
	);

	// Register/net declarations
	// {{{
	localparam	FW = 1 + $clog2(DW/8) + DW;
	reg			lastv;
	wire			r_full, eop_next, r_empty;
	reg	[FW-1:0]	mem	[0:(FLEN-1)];
	reg	[LGFLEN:0]	wr_addr, rd_addr, eop_addr;
	wire	[LGFLEN:0]	fill;
	reg			s_midpacket;
	reg			output_active, abort_incoming;
	reg			m_valid;
	wire	w_wr, w_rd, s_abort, wr_eop;

	assign	w_wr = (S_AXIN_VALID && S_AXIN_READY && !S_AXIN_ABORT)
			&&(!abort_incoming && (!output_active || M_AXIN_VALID));
	assign	w_rd = M_AXIN_VALID && M_AXIN_READY;
	assign	s_abort = S_AXIN_ABORT && s_midpacket;
	assign	wr_eop = w_wr && S_AXIN_LAST;
	// }}}

	// fill
	// {{{
	assign	fill = wr_addr - rd_addr;
	// }}}

	// r_full
	// {{{
	assign	r_full = fill[LGFLEN];
	// }}}

	// S_AXIN_READY
	// {{{
	always @(*)
	if (abort_incoming || S_AXIN_ABORT)
		S_AXIN_READY = 1'b1;
	else if (OPT_WRITE_ON_FULL && output_active && M_AXIN_READY)
		S_AXIN_READY = 1'b1;
	else
		S_AXIN_READY = !r_full;
	// }}}

	// lastv
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		lastv <= 0;	// End of packet pointer is invalid
	else if (wr_eop && (!M_AXIN_READY || !r_empty || !output_active || !OPT_READ_ON_EMPTY))
		lastv <= 1;	// EOP points to valid spot in the FIFO
	else if (w_rd && eop_next)
		lastv <= 0;	// Packet was read, EOP is now invalid
	// }}}

	// eop_addr
	// {{{
	initial	eop_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		eop_addr <= 0;
	else if (wr_eop)
		eop_addr <= wr_addr;
	// }}}

	// eop_next
	// {{{
	assign	eop_next = lastv && (eop_addr == rd_addr);
	// }}}

	// wr_addr, the write address pointer
	// {{{
	initial	wr_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		wr_addr <= 0;
	else if (s_abort)
	begin
		if (lastv)
			wr_addr <= eop_addr + 1;	// Back up to last pkt
		else
			// Empty FIFO, no pkts within it
			wr_addr <= rd_addr + (M_AXIN_VALID ? 1:0);
	end else if (w_wr)
		wr_addr <= wr_addr + 1'b1;
	// }}}

	// Write to memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (w_wr)
		mem[wr_addr[(LGFLEN-1):0]] <= { S_AXIN_LAST,
				S_AXIN_BYTES[$clog2(DW/8)-1:0], S_AXIN_DATA };
	// }}}

	// rd_addr, the read address pointer
	// {{{
	initial	rd_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		rd_addr <= 0;
	else if (w_rd)
		rd_addr <= rd_addr + 1;
	// }}}

	// r_empty
	// {{{
	assign	r_empty = (wr_addr == rd_addr);
	// }}}

	// abort_incoming
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		abort_incoming <= 0;
	else begin
		if (output_active && !M_AXIN_VALID && s_midpacket)
			abort_incoming <= 1;
		if (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST)
			abort_incoming <= 0;
		if (S_AXIN_ABORT && (!S_AXIN_VALID || S_AXIN_READY))
			abort_incoming <= 0;
	end
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && abort_incoming)
		assert(s_midpacket);
`endif
	// }}}

	// output_active
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		output_active <= 0;
	else if (output_active)
	begin
		// We're sending a packet.  Stop sending at the end of the
		// packet
		if (M_AXIN_VALID && M_AXIN_READY && M_AXIN_LAST)
			output_active <= 1'b0;

		// Also, stop sending if we run out of packet
		if (!M_AXIN_VALID)
			output_active <= 1'b0;

		// If we for some reason abort, immediately become inactive
		// ... once the abort completes.  This might take place if
		// we have exhausted our buffer, and we're just dumping straight
		// input to output.  Hence, the ABORT might have come directly
		// from the slave interface.
		if (M_AXIN_ABORT && (!M_AXIN_VALID || M_AXIN_READY))
			output_active <= 1'b0;
	end else if (!M_AXIN_ABORT && ((r_full && !S_AXIN_ABORT) || lastv))
		output_active <= 1'b1;
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && output_active)
		assert(!abort_incoming);
`endif
	// }}}

	// M_AXIN_VALID
	// {{{
	always @(*)
	if (!output_active)
		m_valid = 1'b0;
	else if (OPT_READ_ON_EMPTY && S_AXIN_VALID && !S_AXIN_ABORT)
		m_valid = 1'b1;
	else
		m_valid = !r_empty;

	assign	M_AXIN_VALID = m_valid;
	// }}}

	// M_AXIN_LAST, M_AXIN_BYTES, M_AXIN_DATA: Read from the FIFO
	// {{{
	generate if (OPT_ASYNC_READ && OPT_READ_ON_EMPTY)
	begin : ASYNCHRONOUS_READ_ON_EMPTY
		// M_AXIN_LAST, M_AXIN_DATA
		// {{{
		reg	r_last, last_override;
		reg	[FW-1:0]	memv;

		always @(*)
		begin
			memv = mem[rd_addr[LGFLEN-1:0]];
			if (r_empty)
				memv = { S_AXIN_LAST,
						S_AXIN_BYTES[$clog2(DW/8)-1:0],
						S_AXIN_DATA };
		end

		always @(posedge S_AXI_ACLK)
			last_override <= 0 && (M_AXIN_VALID && !M_AXIN_READY && M_AXIN_LAST);

		assign	M_AXIN_DATA = memv[DW-1:0];
		assign	M_AXIN_BYTES = memv[DW +: $clog2(DW/8)];

		assign	M_AXIN_LAST = memv[FW-1] || last_override;
		// }}}
	end else if (OPT_ASYNC_READ)
	begin : ASYNCHRONOUS_READ
		// M_AXIN_LAST, M_AXIN_DATA
		// {{{
		reg	[FW-1:0]	memv;

		always @(*)
			memv = mem[rd_addr[LGFLEN-1:0]];

		assign	M_AXIN_DATA = memv[DW-1:0];
		assign	M_AXIN_BYTES = memv[DW +: $clog2(DW/8)];

		assign	M_AXIN_LAST = memv[FW-1];
		// }}}
	end else begin : REGISTERED_READ
		// {{{
		reg			bypass_valid;
		reg	[FW-1:0]	bypass_data, rd_data, rdval;
		reg	[LGFLEN-1:0]	rd_next;

		always @(*)
			rd_next = rd_addr[LGFLEN-1:0] + 1;

		// Memory read, bypassing it if we must
		// {{{
		initial bypass_valid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bypass_valid <= 0;
		else begin
			bypass_valid <= 1'b0;
			if (S_AXIN_VALID
				&& (r_empty || (output_active && M_AXIN_READY && (fill == 1))))
				bypass_valid <= 1'b1;
			if (s_abort && !lastv)
				bypass_valid <= 1'b1;
		end

		always @(posedge S_AXI_ACLK)
			bypass_data <= { (S_AXIN_LAST || S_AXIN_ABORT),
				S_AXIN_BYTES[$clog2(DW/8)-1:0], S_AXIN_DATA };

		initial mem[0] = 0;
		initial rd_data = 0;
		always @(posedge S_AXI_ACLK)
		if (bypass_valid || w_rd)
				// (!M_AXIN_VALID || M_AXIN_READY || (M_AXIN_ABORT && !M_AXIN_LAST)))
			rd_data <= mem[(w_rd)?rd_next : rd_addr[LGFLEN-1:0]];

		always @(*)
		if (OPT_READ_ON_EMPTY && r_empty)
			rdval = { S_AXIN_LAST, S_AXIN_BYTES[$clog2(DW/8)-1:0],
							S_AXIN_DATA };
		else if (bypass_valid)
			rdval = bypass_data;
		else
			rdval = rd_data;

		assign	M_AXIN_DATA = rdval[DW-1:0];
		assign	M_AXIN_BYTES = rdval[DW +: $clog2(DW/8)];
		assign	M_AXIN_LAST = rdval[FW-1];
		// }}}
		// }}}
	end endgenerate
	// }}}

	// M_AXIN_ABORT
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		s_midpacket <= 0;
	else if (S_AXIN_ABORT)
		s_midpacket <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
		s_midpacket <= !S_AXIN_LAST;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIN_ABORT <= 1'b0;
	else if (!M_AXIN_ABORT)
	begin
		M_AXIN_ABORT <= !lastv && S_AXIN_ABORT && output_active;
		if (output_active && !M_AXIN_VALID)
			M_AXIN_ABORT <= 1'b1;
	end else if (!M_AXIN_VALID || M_AXIN_READY)
		M_AXIN_ABORT <= 1'b0;
`ifdef	FORMAL
	wire	[LGFLEN:0]	f_fill, f_next;

	always @(*)
	if (S_AXI_ARESETN && M_AXIN_VALID && !M_AXIN_ABORT && !lastv)
		assert(r_empty || s_midpacket);
	always @(*)
	if (S_AXI_ARESETN && !lastv && rd_addr != wr_addr)
	begin
		assert(s_midpacket || (M_AXIN_VALID && M_AXIN_ABORT
				&& wr_addr == f_next));
	end
	always @(*)
	if (S_AXI_ARESETN && abort_incoming && !lastv)
		assert(rd_addr == wr_addr);
	always @(*)
	if (S_AXI_ARESETN && M_AXIN_VALID && M_AXIN_LAST && !M_AXIN_ABORT)
		assert(lastv || (OPT_READ_ON_EMPTY && r_empty && output_active && S_AXIN_VALID && S_AXIN_LAST));
`endif
	// }}}

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, fill, r_empty };
	// verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// FORMAL METHODS
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
`ifdef	FORMAL
	reg			f_past_valid;
	wire			f_full, f_empty;
	(* anyconst *)	reg	fnvr_abort;
	(* anyconst *)	reg	[FW-1:0]	fnvr_data;
	// Verilator lint_off UNDRIVEN
	(* anyconst *)	reg	[LGFLEN:0]	f_first_addr;
	// Verilator lint_on  UNDRIVEN
			reg	[LGFLEN:0]	f_second_addr;
		reg	[FW-1:0]	f_first_data, f_second_data, f_eop_data;

	reg			f_first_addr_in_fifo,  f_first_in_fifo;
	reg			f_second_addr_in_fifo, f_second_in_fifo;
	reg			f_eop_addr_in_fifo;
	reg	[LGFLEN:0]	f_distance_to_first, f_distance_to_second,
				f_distance_to_eop,
				f_first_to_eop, f_second_to_eop;
	reg			f_was_full;
	wire	[9:0]		faxin_swords, faxin_mwords;
	wire	[11:0]		faxin_spkts, faxin_mpkts;
	wire	[LGFLEN:0]	f_eop_next;


	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxin_slave #(
		// {{{
		.DATA_WIDTH(DW),
		.MIN_LENGTH(0)
		// }}}
	) faxins (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIN_VALID(S_AXIN_VALID), .S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA(S_AXIN_DATA), .S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_BYTES(S_AXIN_BYTES),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		//
		.f_stream_word(faxin_swords),
		.f_packets_rcvd(faxin_spkts)
		// }}}
	);

	faxin_master #(
		// {{{
		.DATA_WIDTH(DW),
		.MIN_LENGTH(0), .MAX_LENGTH(0)
		// }}}
	) faxinm (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIN_VALID(M_AXIN_VALID), .S_AXIN_READY(M_AXIN_READY),
		.S_AXIN_DATA(M_AXIN_DATA), .S_AXIN_LAST(M_AXIN_LAST),
		.S_AXIN_BYTES(M_AXIN_BYTES),
		.S_AXIN_ABORT(M_AXIN_ABORT),
		//
		.f_stream_word(faxin_mwords),
		.f_packets_rcvd(faxin_mpkts)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our flags and counters
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	f_fill = wr_addr - rd_addr;
	assign	f_empty = (wr_addr == rd_addr);
	assign	f_full = (f_fill >= (1<<LGFLEN));
	assign	f_next = rd_addr + 1'b1;

	assign	f_eop_next= eop_addr + 1;

	// fill, S_AXIN_READY, M_AXIN_READY, and r_empty
	// {{{
	always @(*)
	begin
		assert(f_fill <= { 1'b1, {(LGFLEN){1'b0}} });
		assert(fill == f_fill);

		assert(r_full  == (f_fill == {1'b1, {(LGFLEN){1'b0}} }));
		assert(r_empty == (f_fill == 0));
		// assert(rd_next == f_next[LGFLEN-1:0]);

		if (!OPT_WRITE_ON_FULL)
		begin
			assert(S_AXIN_READY == (!f_full || S_AXIN_ABORT));
		end else if (!r_full || S_AXIN_ABORT)
		begin
			assert(S_AXIN_READY);
		end else
			assert(S_AXIN_READY == (output_active && M_AXIN_READY));

		if (!OPT_READ_ON_EMPTY)
		begin
			assert(M_AXIN_VALID == (!r_empty && output_active));
		end else
			assert(M_AXIN_VALID == (output_active && (!r_empty || (S_AXIN_VALID && !S_AXIN_ABORT))));
	end
	// }}}

	always @(posedge S_AXI_ACLK)
	if (!OPT_ASYNC_READ && f_past_valid && f_fill == 0)
	begin
		assert(!M_AXIN_VALID || (OPT_READ_ON_EMPTY && S_AXIN_VALID));
	end

	always @(*)
	if (rd_addr != wr_addr)
	begin
		// This also applies for the registered read case
		assert(M_AXIN_ABORT || mem[rd_addr[LGFLEN-1:0]] == {
			M_AXIN_LAST,
			M_AXIN_BYTES[$clog2(DW/8)-1:0], M_AXIN_DATA });
	end else if (OPT_READ_ON_EMPTY)
	begin
		assert(!S_AXIN_LAST || M_AXIN_LAST);
		assert(M_AXIN_DATA == S_AXIN_DATA);
	end

	always @(*)
	if (S_AXI_ARESETN && lastv && !s_midpacket)
		assert(wr_addr == f_eop_next);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Never checks
	// {{{
	always @(*)
	if (fnvr_abort)
	begin
		assume(lastv || !S_AXIN_ABORT);
		assume(lastv || (M_AXIN_VALID || !output_active));
	end

	always @(*)
	if (S_AXI_ARESETN && fnvr_abort)
		assert(!M_AXIN_ABORT);

	always @(*)
	if (S_AXIN_VALID)
		assume({ S_AXIN_LAST, S_AXIN_BYTES, S_AXIN_DATA } != fnvr_data);

	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (f_first_in_fifo)
			assert(f_first_data != fnvr_data);
		if (f_second_in_fifo)
			assert(f_second_data != fnvr_data);

		if (M_AXIN_VALID && (rd_addr != f_first_addr)
				&& (rd_addr != f_second_addr))
		begin
			assume({ M_AXIN_LAST, M_AXIN_BYTES, M_AXIN_DATA } != fnvr_data);
			if (!M_AXIN_LAST)
				assume(M_AXIN_BYTES == 0);
			else
				assume(lastv);
		end
	end

	always @(*)
	if (S_AXI_ARESETN && M_AXIN_VALID && !M_AXIN_ABORT)
		assert({ M_AXIN_LAST, M_AXIN_BYTES, M_AXIN_DATA } != fnvr_data);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Formal contract: (Twin write test)
	// {{{
	// If you write two values in succession, you should be able to read
	// those same two values in succession some time later.
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
		f_second_addr = f_first_addr + 1;

	// f_distance_to_first, f_first_addr_in_fifo
	// {{{
	always @(*)
	begin
		f_distance_to_first = (f_first_addr - rd_addr);
		f_first_addr_in_fifo = 0;
		if ((f_fill != 0) && (f_distance_to_first < f_fill))
			f_first_addr_in_fifo = 1;
	end
	// }}}

	// f_distance_to_second, f_second_addr_in_fifo
	// {{{
	always @(*)
	begin
		f_distance_to_second = (f_second_addr - rd_addr);
		f_second_addr_in_fifo = 0;
		if ((f_fill != 0) && (f_distance_to_second < f_fill))
			f_second_addr_in_fifo = 1;
	end
	// }}}

	// f_distance_to_eop, f_eop_addr_in_fifo
	// {{{
	always @(*)
	begin
		f_distance_to_eop = (eop_addr - rd_addr);
		f_eop_addr_in_fifo = 0;
		if ((f_fill != 0) && (f_distance_to_eop < f_fill))
			f_eop_addr_in_fifo = 1;
	end
	// }}}

	// f_first_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (w_wr && wr_addr == f_first_addr)
		f_first_data <= { S_AXIN_LAST, S_AXIN_BYTES[$clog2(DW/8)-1:0],
					S_AXIN_DATA };
	// }}}

	// f_second_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (w_wr && wr_addr == f_second_addr)
		f_second_data <= { S_AXIN_LAST, S_AXIN_BYTES[$clog2(DW/8)-1:0],
				S_AXIN_DATA };
	// }}}

	// f_first_data checks
	// {{{
	always @(*)
	if (f_first_addr_in_fifo)
		assert(mem[f_first_addr[LGFLEN-1:0]] == f_first_data);
	always @(*)
	if (f_first_addr_in_fifo && lastv && f_first_addr == eop_addr)
		assert(mem[f_first_addr[LGFLEN-1:0]][FW-1]);
	always @(*)
		f_first_in_fifo = (f_first_addr_in_fifo && (mem[f_first_addr[LGFLEN-1:0]] == f_first_data));
	always @(*)
	if (f_first_in_fifo && f_first_data[FW-1])
		assert(lastv || (M_AXIN_VALID && M_AXIN_LAST && f_first_addr == rd_addr));
	always @(*)
	if (f_first_in_fifo && !f_first_data[FW-1])
		assert(f_first_data[DW +: $clog2(DW/8)] == 0);
	// }}}

	// f_second_data checks
	// {{{
	always @(*)
	if (f_second_addr_in_fifo)
		assert(mem[f_second_addr[LGFLEN-1:0]] == f_second_data);
	always @(*)
	if (f_second_addr_in_fifo && lastv && f_second_addr == eop_addr)
		assert(mem[f_second_addr[LGFLEN-1:0]][FW-1]);

	always @(*)
		f_second_in_fifo = (f_second_addr_in_fifo && (mem[f_second_addr[LGFLEN-1:0]] == f_second_data));
	always @(*)
	if (f_second_in_fifo && f_second_data[FW-1])
		assert(lastv || (M_AXIN_VALID && M_AXIN_LAST && f_second_addr == rd_addr));
	always @(*)
	if (f_second_in_fifo && !f_second_data[FW-1])
		assert(f_second_data[DW +: $clog2(DW/8)] == 0);
	// }}}

	// EOP checks
	// {{{
	always @(*)
		f_first_to_eop  = (eop_addr - f_first_addr);
	always @(*)
		f_second_to_eop = (eop_addr - f_second_addr);

	always @(*)
		f_eop_data = mem[eop_addr[LGFLEN-1:0]];

	always @(*)
	if (S_AXI_ARESETN)
	begin
		if(lastv)
		begin
			assert(f_eop_addr_in_fifo);
			assert(f_eop_data[FW-1]);

			if (f_first_in_fifo && f_first_data[FW-1])
				assert(f_first_to_eop < (1<<LGFLEN));
			if (f_second_in_fifo && f_second_data[FW-1])
				assert(f_second_to_eop < (1<<LGFLEN));
		end else begin
			assert(!f_eop_addr_in_fifo || !f_eop_data[FW-1]
				|| (eop_addr == rd_addr && M_AXIN_VALID && M_AXIN_LAST));
			if (f_first_in_fifo)
				assert(!f_first_data[FW-1]
					||(f_first_addr == rd_addr && M_AXIN_VALID && M_AXIN_LAST));
			if (f_second_in_fifo)
				assert(!f_second_data[FW-1]
					||(f_second_addr == rd_addr && M_AXIN_VALID && M_AXIN_LAST));
		end
	end
	// }}}

	// Twin write state machine
	// {{{
	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN))
	begin
		case({$past(f_first_in_fifo), $past(f_second_in_fifo)})
		2'b00: begin
				// {{{
				if ($past(w_wr && (!w_rd || !r_empty))
					&&($past(wr_addr == f_first_addr)))
				begin
					assert(f_first_in_fifo);
				end else
					assert(!f_first_in_fifo);
				//
				// The second could be in the FIFO, since
				// one might write other data than f_first_data
				//
				// assert(!f_second_in_fifo);
			end
			// }}}
		2'b01: begin
				// {{{
				assert(!f_first_in_fifo);
				if ($past(w_rd && (rd_addr==f_second_addr)))
				begin
					assert((!M_AXIN_READY&&!OPT_ASYNC_READ)||!f_second_in_fifo);
				end else if (!$past(s_midpacket) || !$past(S_AXIN_ABORT))
					assert(f_second_in_fifo);
			end
			// }}}
		2'b10: begin
				// {{{
				if ($past(w_wr)
					&&($past(wr_addr == f_second_addr)))
				begin
					assert(f_second_in_fifo);
				end else
					assert(!f_second_in_fifo);
				if ((!$past(S_AXIN_ABORT)) // || $past(lastv))
					&& ($past(!w_rd ||(rd_addr != f_first_addr))))
					assert(f_first_in_fifo);
			end
			// }}}
		2'b11: begin
			// {{{
				if (!$past(S_AXIN_ABORT) && !M_AXIN_ABORT) // || $past(lastv))
				begin
					assert(f_second_in_fifo);
					if ($past(!w_rd ||!output_active || (rd_addr != f_first_addr)))
					begin
						assert(f_first_in_fifo);
						if (rd_addr == f_first_addr)
							assert({ M_AXIN_LAST, M_AXIN_BYTES, M_AXIN_DATA } == f_first_data);
					end else begin
						assert(!f_first_in_fifo);
						assert({ M_AXIN_LAST, M_AXIN_BYTES, M_AXIN_DATA } == f_second_data);
					end
				end
			end
			// }}}
		endcase
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//	Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	f_was_full = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXIN_READY)
		f_was_full <= 1;

`ifdef	PKTGATE
	always @(posedge S_AXI_ACLK)
		cover($fell(f_empty));

	always @(posedge S_AXI_ACLK)
		cover($fell(!M_AXIN_READY));

	always @(posedge S_AXI_ACLK)
		cover(f_was_full && f_empty);

	always @(posedge S_AXI_ACLK)
		cover($past(!S_AXIN_READY,2)&&(!$past(!S_AXIN_READY))&&(!S_AXIN_READY));

	always @(posedge S_AXI_ACLK)
	if (f_past_valid)
		cover($past(!M_AXIN_READY,2)&&(!$past(!M_AXIN_READY))&& !M_AXIN_READY);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//	Simplifying assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// always @(*)
	//	assume(!S_AXIN_ABORT);

	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, f_was_full, faxin_spkts, faxin_mpkts,
			faxin_swords, faxin_mwords, f_empty, f_next };
	// Verilator lint_on  UNUSED
	// }}}
`endif // FORMAL
// }}}
endmodule
