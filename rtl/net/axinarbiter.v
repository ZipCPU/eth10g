////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axinarbiter.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Arbitrates from among NIN packet sources to select and forward
//		one of those sources forward.
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
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module axinarbiter #(
		// {{{
		parameter	NIN = 4,	// Number of incoming eth ports
		parameter	DW = 64,	// Bits per clock cycle
		parameter [0:0]	OPT_LOWPOWER = 0
		// }}}
	) (
		// {{{
		input	wire				i_clk, i_reset,
		// Incoming packets from all interfaces
		// {{{
		input	wire	[NIN-1:0]		S_VALID,
		output	wire	[NIN-1:0]		S_READY,
		input	wire	[NIN*DW-1:0]		S_DATA,
		input	wire	[NIN*$clog2(DW)-1:0]	S_BYTES,
		input	wire	[NIN-1:0]		S_LAST,
		input	wire	[NIN-1:0]		S_ABORT,
		// }}}
		// Outgoing packet
		// {{{
		output	reg			M_VALID,
		input	wire			M_READY,
		output	reg	[DW-1:0]	M_DATA,
		output	reg [$clog2(DW)-1:0]	M_BYTES,
		output	reg			M_LAST,
		output	reg			M_ABORT
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	genvar			gk;
	integer			ik;

	reg	[NIN-1:0]	grant;
	wire	[NIN-1:0]	midpkt;
	reg	[DW-1:0]	merged_data;
	reg [$clog2(DW)-1:0]	merged_bytes;
	reg			merged_last;
	wire			stalled;
	// }}}

	pktarbiter #(
		.W(NIN)
	) u_arbiter (
		// {{{
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.i_req(S_VALID), .i_stall(stalled),
		.o_grant(grant)
		// }}}
	);

	generate for(gk=0; gk<NIN; gk=gk+1)
	begin : GEN_MIDPKT
		reg	r_midpkt;

		always @(posedge i_clk)
		if (i_reset)
			r_midpkt <= 0;
		else if (S_ABORT[gk] && (!S_VALID[gk] || S_LAST[gk]))
			r_midpkt <= 1'b0;
		else if (S_VALID[gk] && S_READY[gk])
			r_midpkt <= !S_LAST[gk];

		assign	midpkt[gk] = r_midpkt;
	end endgenerate

	assign	stalled = |midpkt;
	assign	S_READY = (!M_VALID || M_READY) ? grant : 0;

	// M_VALID
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		M_VALID <= 0;
	else if (!M_VALID && M_READY)
		M_VALID <= |(S_VALID & S_READY);
	// }}}

	// merged_data, merged_bytes, merged_last
	// {{{
	always @(*)
	begin
		merged_data  = 0;
		merged_bytes = 0;
		merged_last  = 0;

		for(ik=0; ik<NIN; ik=ik+1)
		if (grant[ik])
		begin
			merged_data  = merged_data  | S_DATA[ik * DW +: DW];
			merged_bytes = merged_bytes
				| S_BYTES[ik * $clog2(DW) +: $clog2(DW)];
			merged_last  = merged_last  | S_LAST[ik];
		end
	end
	// }}}

	// M_DATA, M_BYTES, M_LAST
	// {{{
	always @(posedge i_clk)
	if (i_reset && OPT_LOWPOWER)
	begin
		M_DATA  <= 0;
		M_BYTES <= 0;
		M_LAST  <= 0;
	end else if (!M_VALID || M_READY)
	begin
		M_DATA  <= merged_data;
		M_BYTES <= merged_bytes;
		M_LAST  <= merged_last;

		if (OPT_LOWPOWER && (S_VALID & S_READY & ~S_ABORT) == 0)
		begin
			M_DATA  <= 0;
			M_BYTES <= 0;
			M_LAST  <= 0;
		end
	end
	// }}}

	// M_ABORT
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		M_ABORT <= 0;
	else if (!(M_VALID && !M_READY && M_LAST && !M_ABORT))
		M_ABORT <= 0;
	else if (|(S_ABORT & grant & (~S_VALID | S_READY)))
		M_ABORT <= 1'b1;
	else if (!M_VALID || M_READY)
		M_ABORT <= 1'b0;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
