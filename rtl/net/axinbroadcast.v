////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axinbroadcast.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Broadcasts a packet from a single source to NIN destinations.
//		Actual chosen destination is selectable.  Does not include
//	any FIFOs--those can follow if necessary.
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
module axinbroadcast #(
		// {{{
		parameter	NOUT = 4,	// Number of incoming eth ports
		parameter	DW = 64,	// Bits per clock cycle
		parameter [0:0]	OPT_SKIDBUFFER = 0,
		parameter [0:0]	OPT_LOWPOWER = 0
		// }}}
	) (
		// {{{
		input	wire				i_clk, i_reset,
		// Incoming packet interface
		// {{{
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[DW-1:0]	S_DATA,
		input	wire [$clog2(DW)-1:0]	S_BYTES,
		input	wire			S_LAST,
		input	wire			S_ABORT,
		//
		input	wire [NOUT-1:0]		S_PORT,
		// }}}
		// Outgoing packet, forwarded to NOUT interfaces
		// {{{
		output	reg	[NOUT-1:0]		M_VALID,
		input	wire	[NOUT-1:0]		M_READY,
		output	reg	[NOUT*DW-1:0]		M_DATA,
		output	reg [NOUT*$clog2(DW)-1:0]	M_BYTES,
		output	reg	[NOUT-1:0]		M_LAST,
		output	reg	[NOUT-1:0]		M_ABORT
		// }}}
		// }}}
	);

	genvar	gk;
	wire				skd_valid, skd_ready,
					skd_last, skd_abort;
	wire	[DW-1:0]		skd_data;
	wire	[$clog2(DW)-1:0]	skd_bytes;
	wire	[NOUT-1:0]		skd_port;

	////////////////////////////////////////////////////////////////////////
	//
	// Start with a skidbuffer
	// {{{
	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER

		netskid #(
			.DW(NOUT+DW+$clog2(DW))
		) u_skidbuffer (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.S_AXIN_VALID(S_VALID), .S_AXIN_READY(S_READY),
			.S_AXIN_DATA({ S_PORT, S_BYTES, S_DATA }),
			.S_AXIN_LAST(S_LAST), .S_AXIN_ABORT(S_ABORT),
			//
			.M_AXIN_VALID(skd_valid), .M_AXIN_READY(skd_ready),
			.M_AXIN_DATA({ skd_port, skd_bytes, skd_data }),
			.M_AXIN_LAST(skd_last), .M_AXIN_ABORT(skd_abort)
			// }}}
		);
	end else begin : NO_SKIDBUFFER

		assign	skd_valid = S_VALID;
		assign	S_READY   = skd_ready;
		assign	skd_data  = S_DATA;
		assign	skd_bytes = S_BYTES;
		assign	skd_last  = S_LAST;
		assign	skd_abort = S_ABORT;
		assign	skd_port  = S_PORT;

	end endgenerate

	assign	skd_ready = (0 == (M_VALID & ~M_READY & S_PORT));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate the outputs
	// {{{

	// M_*
	generate for(gk=0; gk<NOUT; gk=gk+1)
	begin : GEN_OUT
		// {{{
		always @(posedge i_clk)
		if (i_reset)
			M_VALID[gk] <= 0;
		else if (!M_VALID[gk] || M_READY[gk])
			M_VALID[gk] <= skd_valid && skd_ready && skd_port[gk]
						&& !skd_abort;

		always @(posedge i_clk)
		if (OPT_LOWPOWER && i_reset)
		begin
			M_DATA[ gk*DW +: DW] <= 0;
			M_BYTES[gk*$clog2(DW) +: $clog2(DW)] <= 0;
			M_LAST[ gk] <= 1'b0;
		end else if (!M_VALID[gk] || M_READY[gk])
		begin
			M_DATA[ gk*DW +: DW] <= skd_data;
			M_BYTES[gk*$clog2(DW) +: $clog2(DW)] <= skd_bytes;
			M_LAST[ gk] <= skd_last;

			if (OPT_LOWPOWER && (!skd_valid || !skd_port[gk]))
			begin
				M_DATA[ gk*DW +: DW] <= 0;
				M_BYTES[gk*$clog2(DW) +: $clog2(DW)] <= 0;
				M_LAST[ gk] <= 1'b0;
			end
		end

		always @(posedge i_clk)
		if (i_reset)
		begin
			M_ABORT[gk] <= 0;
		end else if (skd_abort && skd_port[gk]
					&& (!skd_valid || skd_ready))
			M_ABORT[gk] <= 1'b1;
		else if (M_READY[gk])
			M_ABORT[gk] <= 1'b0;
		// }}}
	end endgenerate

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
