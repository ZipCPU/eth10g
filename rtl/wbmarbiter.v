////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbmarbiter.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A basic asynchronous FIFO.
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
`default_nettype	none
// }}}
module wbmarbiter #(
		// {{{
		parameter	DW = 64,
		parameter	AW = 31-$clog2(DW/8),
		parameter	NIN = 4,
		parameter	LGFIFO = 5,
		parameter [0:0]	OPT_LOWPOWER = 0
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire	[NIN-1:0]	s_cyc, s_stb, s_we,
		input	wire	[NIN*AW-1:0]	s_addr,
		input	wire	[NIN*DW-1:0]	s_data,
		input	wire	[NIN*DW/8-1:0]	s_sel,
		output	wire	[NIN-1:0]	s_stall, s_ack,
		output	wire	[NIN*DW-1:0]	s_idata,
		output	wire	[NIN-1:0]	s_err,
		//
		output	reg			m_cyc, m_stb, m_we,
		output	reg	[AW-1:0]	m_addr,
		output	reg	[DW-1:0]	m_data,
		output	reg	[DW/8-1:0]	m_sel,
		input	wire			m_stall, m_ack,
		input	wire	[DW-1:0]	m_idata,
		input	wire			m_err
		// }}}
	);

	// Register/net declarations
	// {{{
	genvar			gk;
	integer			ik;

	wire			arb_stall;
	wire	[NIN-1:0]	grant;
	reg	[NIN-1:0]	ack, err;
	reg	[DW-1:0]	data;

	wire			fifo_reset;
	wire			ack_wr, ack_rd;
	reg	[LGFIFO:0]	fif_wraddr, fif_rdaddr;
	wire	[LGFIFO:0]	ack_fill;
	wire			ack_empty, ack_full;
	wire	[NIN-1:0]	ack_fifo_data;

	reg	[NIN-1:0]	flushing;

	reg			nxt_stb, nxt_we;
	reg	[AW-1:0]	nxt_addr;
	reg	[DW-1:0]	nxt_data;
	reg	[DW/8-1:0]	nxt_sel;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Arbitrate among sources
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	pktarbiter #(
		.W(NIN)
	) u_arb (
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.i_req(s_stb & ~flushing), .i_stall(arb_stall),
		.o_grant(grant)
	);

	assign	arb_stall = m_stb && m_stall;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Log STBs, to know where to deliver ACKs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	fifo_reset = i_reset || (m_cyc && m_err);
	assign	ack_wr =|(s_stb & ~s_stall);
	assign	ack_rd = m_ack;

	sfifo #(
		.BW(NIN),
		.LGFLEN(LGFIFO)
	) u_ack_fifo (
		// {{{
		.i_clk(i_clk), .i_reset(fifo_reset),
		.i_wr(ack_wr), .i_data(grant),
		.o_full(ack_full), .o_fill(ack_fill),
		.i_rd(ack_rd), .o_data(ack_fifo_data),
		.o_empty(ack_empty)
		// }}}
	);

	always @(posedge i_clk)
	if (fifo_reset)
		fif_wraddr <= 0;
	else if (ack_wr && !ack_full)
		fif_wraddr <= fif_wraddr + 1;

	always @(posedge i_clk)
	if (fifo_reset)
		fif_rdaddr <= 0;
	else if (ack_rd && !ack_empty)
		fif_rdaddr <= fif_rdaddr + 1;

	// Need to do some extra work, just to deal with potential bus errors
	// and dropped CYC lines
	initial	ack = 0;
	initial	err = 0;
	generate for(gk=0; gk<NIN; gk=gk+1)
	begin : FLUSH_ACKS
		// At issue is the fact that, if the slave drops CYC, we need
		// to abort any ongoing transactions.  Likewise, if the master
		// returns a bus error--we'll also need to abort any ongoing
		// transactions.  In both of those cases we need to make sure
		// nothing in the FIFO is returned to this slave as an ACK from
		// any outstanding transactions.
		reg			empty;
		reg	[LGFIFO:0]	last_addr;

		always @(posedge i_clk)
		if (fifo_reset)
			last_addr <= 0;
		else if (ack_empty || s_stb[gk] && !s_stall[gk])
			last_addr <= fif_wraddr;
		else if (ack_rd && last_addr == fif_rdaddr)
			last_addr <= fif_rdaddr + 1;

		initial	empty = 1;
		always @(posedge i_clk)
		if (fifo_reset || !s_cyc[gk])
			empty <= 1;
		else if (s_stb[gk] && !s_stall[gk])
			empty <= 1'b0;
		else if (ack_empty)
			empty <= 1;
		else if (ack_rd && last_addr == fif_rdaddr)
			empty <= 1;

		always @(posedge i_clk)
		if (fifo_reset)
			flushing[gk] <= 0;
		else if (ack_empty || (m_ack && last_addr == fif_rdaddr))
			flushing[gk] <= 0;
		else if (!s_cyc[gk])
			flushing[gk] <= 1;

		assign	s_stall[gk] = flushing[gk] || (grant != (1<<gk))
				|| ack_full || (m_stb && m_stall)
				|| (m_cyc && m_err);

		// initial	ack[gk] = 0;
		always @(posedge i_clk)
		if (i_reset || !m_cyc || !s_cyc[gk] || empty)
			ack[gk] <= 0;
		else
			ack[gk] <= m_ack && ack_fifo_data[gk];

		always @(posedge i_clk)
		if (i_reset || !m_cyc || !s_cyc[gk])
			err[gk] <= 0;
		else if (empty && (!s_stb[gk] || s_stall[gk]))
			err[gk] <= 0;
		else if (m_err && !ack_empty)
			err[gk] <= 1'b1;

`ifdef	FORMAL
		always @(*)
		if (ack_empty)
			assert(empty);
`endif
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// m_*: Generate downstram outputs
	// {{{

	initial	m_cyc = 1'b0;
	always @(posedge i_clk)
	if (fifo_reset)
		m_cyc <= 1'b0;
	else if (ack_wr)
		m_cyc <= 1'b1;
	else if (m_cyc && m_ack && ack_fill == 1)
		m_cyc <= 1'b0;

	always @(*)
	begin
		nxt_stb  = |(s_stb & ~s_stall & ~s_err);
		nxt_we   = 0;
		nxt_addr = 0;
		nxt_data = 0;
		nxt_sel  = 0;
		for(ik=0; ik<NIN; ik=ik+1)
		if (grant[ik])
		begin
			nxt_we   = nxt_we   | s_we[ik];
			nxt_addr = nxt_addr | s_addr[ik * AW   +: AW  ];
			nxt_data = nxt_data | s_data[ik * DW   +: DW  ];
			nxt_sel  = nxt_sel  | s_sel[ ik * DW/8 +: DW/8];
		end
	end

	initial	m_stb = 1'b0;
	always @(posedge i_clk)
	if (fifo_reset)
		m_stb <= 1'b0;
	else if (!m_stb || !m_stall)
		m_stb <= nxt_stb;

	always @(posedge i_clk)
	if (OPT_LOWPOWER && fifo_reset)
	begin
		m_addr <= 0;
		m_data <= 0;
		m_sel  <= 0;
	end else if (!m_stb || !m_stall)
	begin
		m_we   <= nxt_we;
		m_addr <= nxt_addr;
		m_data <= nxt_data;
		m_sel  <= nxt_sel;

		if (OPT_LOWPOWER && !nxt_stb)
		begin
			m_we   <= 1'b0;
			m_addr <= {(AW  ){1'b0}};
			m_data <= {(DW  ){1'b0}};
			m_sel  <= {(DW/8){1'b0}};
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// s_*: Generate return data
	// {{{
	assign	s_ack = ack;
	assign	s_err = err;

	always @(posedge i_clk)
		data <= m_idata;

	assign	s_err = {(NIN){err}};
	assign	s_idata = {(NIN){data}};
	// }}}

	// Keep Verilator happy
	// {{{
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
	localparam	F_LGDEPTH = LGFIFO+1;
	reg			f_past_valid;
	wire	[F_LGDEPTH-1:0]	fwbm_nreqs, fwbm_nacks, fwbm_outstanding;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	generate for(gk=0; gk<NIN; gk=gk+1)
	begin : GEN_FWBSLAVE
		wire	[F_LGDEPTH-1:0]	fwbs_nreqs, fwbs_nacks,
					fwbs_outstanding;

		fwb_slave #(
			.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH)
		) fwb (
			// {{{
				.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(s_cyc[gk]), .i_wb_stb(s_stb[gk]),
					.i_wb_we(s_we[gk]),
			.i_wb_addr(s_addr[gk*AW +: AW]),
				.i_wb_data(s_data[gk*DW +: DW]),
				.i_wb_sel(s_sel[gk*DW/8 +: DW/8]),
			.i_wb_ack(s_ack[gk]), .i_wb_stall(s_stall[gk]),
			.i_wb_idata(s_idata[gk*DW +: DW]),
			.i_wb_err(s_err[gk]),
			.f_nreqs(fwbs_nreqs),
			.f_nacks(fwbs_nacks),
			.f_outstanding(fwbs_outstanding)
			// }}}
		);

	end endgenerate

	fwb_master #(
		.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH)
	) fwb_m (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(m_cyc), .i_wb_stb(m_stb), .i_wb_we(1'b0 && m_we),
		.i_wb_addr(m_addr), .i_wb_data(m_data), .i_wb_sel(m_sel),
		.i_wb_ack(m_ack), .i_wb_stall(m_stall), .i_wb_idata(m_idata),
		.i_wb_err(m_err),
		.f_nreqs(fwbm_nreqs),
		.f_nacks(fwbm_nacks),
		.f_outstanding(fwbm_outstanding)
		// }}}
	);
	////////////////////////////////////////////////////////////////////////
	//
	// OPT_LOWPOWER
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_LOWPOWER)
	begin
		always @(*)
		if (!i_reset && !m_stb)
		begin
			assert(m_we   == 1'b0);
			assert(m_addr == {(AW){1'b0}});
			assert(m_data == {(DW){1'b0}});
			assert(m_sel  == {(DW/8){1'b0}});
		end

	end endgenerate

	// }}}
`endif
// }}}
endmodule
