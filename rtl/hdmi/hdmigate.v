////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/hdmigate.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Accepts packets which cannot stall, produces packets which can.
//		Packets are quietly held in the buffer until a full packet is
//	ready.  If any packet overflows the buffer, the packet will be aborted,
//	and not forwarded.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
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
`default_nettype none
// }}}
module	hdmigate #(
		// {{{
		parameter	BW=8,		// Byte/data width
		parameter 	LGFLEN=5,	// Minimum: one packet
		parameter [0:0]	OPT_ASYNC_READ = 1'b1,
		parameter [0:0]	OPT_WRITE_ON_FULL = 1'b0,
		parameter [0:0]	OPT_READ_ON_EMPTY = 1'b0,
		localparam	FLEN=(1<<LGFLEN)
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,
		// Verilator lint_off SYNCASYNCNET
		input	wire		S_AXI_ARESETN,
		// Verilator lint_on  SYNCASYNCNET
		//
		// Write interface
		input	wire		S_AXIN_VALID,
		input	wire [BW-1:0]	S_AXIN_DATA,
		input	wire		S_AXIN_LAST,
		//
		// Read interface
		output	reg		M_AXIN_VALID,
		input	wire		M_AXIN_READY,
		output	reg [BW-1:0]	M_AXIN_DATA,
		output	reg		M_AXIN_LAST
		// }}}
	);

	// Register/net declarations
	// {{{
	wire			S_AXIN_READY; // , S_AXIN_ABORT;
	reg			lastv;
	wire			r_full, eop_next, r_empty;
	reg	[BW:0]		mem	[0:(FLEN-1)];
	reg	[LGFLEN:0]	wr_addr, rd_addr, eop_addr, load;
	wire	[LGFLEN:0]	fill;
	reg			s_midpacket, s_aborting;

	wire	w_wr = (S_AXIN_VALID && S_AXIN_READY) && !s_aborting;
	wire	w_rd = (M_AXIN_VALID && M_AXIN_READY);
	wire	s_abort = s_aborting
			|| ((S_AXIN_VALID && !S_AXIN_READY) && s_midpacket);
	// assign	S_AXIN_ABORT = S_AXIN_VALID && !S_AXIN_READY;
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
	assign	S_AXIN_READY = (OPT_WRITE_ON_FULL && M_AXIN_VALID
						&& M_AXIN_READY) || !r_full;
	// }}}

	// lastv
	// {{{
	initial	lastv = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		lastv <= 0;	// End of packet pointer is invalid
	else if (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST
					&& (!r_empty || !M_AXIN_READY))
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
	else if (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST)
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
		else if (M_AXIN_VALID)
			wr_addr <= rd_addr + 1;	// Empty FIFO, no pkts within it
	end else if (w_wr)
		wr_addr <= wr_addr + 1'b1;
	// }}}

	// Write to memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (w_wr)
		mem[wr_addr[(LGFLEN-1):0]] <= { S_AXIN_LAST, S_AXIN_DATA };
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

	// M_AXIN_LAST, M_AXIN_DATA: Read from the FIFO
	// {{{
	generate if (OPT_ASYNC_READ && OPT_READ_ON_EMPTY)
	begin : ASYNCHRONOUS_READ_ON_EMPTY
		// M_AXIN_LAST, M_AXIN_DATA
		// {{{

		always @(*)
		begin
			{ M_AXIN_LAST, M_AXIN_DATA } = mem[rd_addr[LGFLEN-1:0]];
			if (r_empty)
				{ M_AXIN_LAST, M_AXIN_DATA } = { S_AXIN_LAST, S_AXIN_DATA };
		end

		// }}}
	end else if (OPT_ASYNC_READ)
	begin : ASYNCHRONOUS_READ
		// M_AXIN_LAST, M_AXIN_DATA
		// {{{
		always @(*)
			{ M_AXIN_LAST, M_AXIN_DATA } = mem[rd_addr[LGFLEN-1:0]];
		// }}}
	end else begin : REGISTERED_READ
		// {{{
		reg			bypass_valid;
		reg	[BW:0]		bypass_data, rd_data;
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
				&& (r_empty || (M_AXIN_READY && (fill == 1))))
				bypass_valid <= 1'b1;
			if (s_abort && !lastv)
				bypass_valid <= 1'b1;
		end

		always @(posedge S_AXI_ACLK)
			bypass_data <= { S_AXIN_LAST, S_AXIN_DATA };

		initial mem[0] = 0;
		initial rd_data = 0;
		always @(posedge S_AXI_ACLK)
		if (bypass_valid || w_rd)
			rd_data <= mem[(w_rd)?rd_next : rd_addr[LGFLEN-1:0]];

		always @(*)
		if (OPT_READ_ON_EMPTY && r_empty)
			{ M_AXIN_LAST, M_AXIN_DATA } = { S_AXIN_LAST, S_AXIN_DATA };
		else if (bypass_valid)
			{ M_AXIN_LAST, M_AXIN_DATA } = bypass_data;
		else
			{ M_AXIN_LAST, M_AXIN_DATA } = rd_data;
		// }}}
		// }}}
	end endgenerate
	// }}}

	initial	{ s_aborting, s_midpacket } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ s_aborting, s_midpacket } <= 0;
	else if (S_AXIN_VALID)
	begin
		s_midpacket <= 1'b1;
		if (r_full)
			s_aborting <= 1'b1;

		if (S_AXIN_LAST)
			{ s_aborting, s_midpacket } <= 2'b00;
	end

	// load
	// {{{
	initial	load = 0;
	initial	M_AXIN_VALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		load <= 0;
		M_AXIN_VALID <= 1'b0;
	end else case({ (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST),
				(M_AXIN_VALID && M_AXIN_READY && M_AXIN_LAST) })
	2'b10: begin
		load <= load + 1;
		M_AXIN_VALID <= 1'b1;
		end
	2'b01: begin
		load <= load - 1;
		M_AXIN_VALID <= (load > 1);
		end
	default: begin end
	endcase
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

//
// Assumptions about our input(s)
//
//
`ifdef	SFIFO
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	reg			f_past_valid;
	wire	[LGFLEN:0]	f_fill, f_next;
	wire			f_full, f_empty;

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

	wire	[9:0]	faxin_swords, faxin_mwords;
	wire	[11:0]	faxin_spkts, faxin_mpkts;

	faxin_slave #(
		// {{{
		.DATA_WIDTH(BW),
		.MIN_LENGTH(0)
		// }}}
	) faxins (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIN_VALID(S_AXIN_VALID), .S_AXIN_READY(1'b1),
		.S_AXIN_DATA(S_AXIN_DATA), .S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_VALID && r_full),
		//
		.f_stream_word(faxin_swords),
		.f_packets_rcvd(faxin_spkts)
		// }}}
	);

	faxin_master #(
		// {{{
		.DATA_WIDTH(BW),
		.MIN_LENGTH(0), .MAX_LENGTH(0)
		// }}}
	) faxinm (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIN_VALID(M_AXIN_VALID), .S_AXIN_READY(M_AXIN_READY),
		.S_AXIN_DATA(M_AXIN_DATA), .S_AXIN_LAST(M_AXIN_LAST),
		.S_AXIN_ABORT(1'b0),
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
		end else
			assert(S_AXIN_READY == (!r_full || S_AXIN_ABORT || M_AXIN_READY));

		if (!OPT_READ_ON_EMPTY)
		begin
			assert(M_AXIN_VALID == !r_empty);
		end else
			assert(M_AXIN_VALID == !r_empty || (S_AXIN_VALID && !S_AXIN_ABORT));
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
		assert(mem[rd_addr[LGFLEN-1:0]] == { M_AXIN_LAST, M_AXIN_DATA });
	end else if (OPT_READ_ON_EMPTY)
	begin
		assert(!S_AXIN_LAST || M_AXIN_LAST);
		assert(M_AXIN_DATA == S_AXIN_DATA);
	end

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
	// Verilator lint_off UNDRIVEN
	(* anyconst *)	reg	[LGFLEN:0]	f_first_addr;
	// Verilator lint_on  UNDRIVEN
			reg	[LGFLEN:0]	f_second_addr;
			reg	[BW:0]	f_first_data, f_second_data, f_eop_data;

	reg			f_first_addr_in_fifo,  f_first_in_fifo;
	reg			f_second_addr_in_fifo, f_second_in_fifo;
	reg			f_eop_addr_in_fifo;
	reg	[LGFLEN:0]	f_distance_to_first, f_distance_to_second,
				f_distance_to_eop,
				f_first_to_eop, f_second_to_eop;

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
		f_first_data <= { S_AXIN_LAST, S_AXIN_DATA };
	// }}}

	// f_second_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (w_wr && wr_addr == f_second_addr)
		f_second_data <= { S_AXIN_LAST, S_AXIN_DATA };
	// }}}

	// f_first_data checks
	// {{{
	always @(*)
	if (f_first_addr_in_fifo)
		assert(mem[f_first_addr[LGFLEN-1:0]] == f_first_data);
	always @(*)
	if (f_first_addr_in_fifo && lastv && f_first_addr == eop_addr)
		assert(mem[f_first_addr[LGFLEN-1:0]][BW]);
	always @(*)
		f_first_in_fifo = (f_first_addr_in_fifo && (mem[f_first_addr[LGFLEN-1:0]] == f_first_data));
	// }}}

	// f_second_data checks
	// {{{
	always @(*)
	if (f_second_addr_in_fifo)
		assert(mem[f_second_addr[LGFLEN-1:0]] == f_second_data);
	always @(*)
	if (f_second_addr_in_fifo && lastv && f_second_addr == eop_addr)
		assert(mem[f_second_addr[LGFLEN-1:0]][BW]);

	always @(*)
		f_second_in_fifo = (f_second_addr_in_fifo && (mem[f_second_addr[LGFLEN-1:0]] == f_second_data));
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
	if (S_AXI_ARESETN && lastv)
	begin
		assert(f_eop_addr_in_fifo);
		assert(f_eop_data[BW]);

		if (f_first_in_fifo && f_first_data[BW])
			assert(f_first_to_eop < (1<<LGFLEN));
		if (f_second_in_fifo && f_second_data[BW])
			assert(f_second_to_eop < (1<<LGFLEN));
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
				end else
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
				if (!$past(S_AXIN_ABORT)) // || $past(lastv))
				begin
					assert(f_second_in_fifo);
					if ($past(!w_rd ||(rd_addr != f_first_addr)))
					begin
						assert(f_first_in_fifo);
						if (rd_addr == f_first_addr)
							assert({ M_AXIN_LAST, M_AXIN_DATA } == f_first_data);
					end else begin
						assert(!f_first_in_fifo);
						assert({ M_AXIN_LAST, M_AXIN_DATA } == f_second_data);
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
	reg	f_was_full;
	initial	f_was_full = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXIN_READY)
		f_was_full <= 1;

`ifdef	SFIFO
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
