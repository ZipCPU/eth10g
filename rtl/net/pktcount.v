////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pktcount.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generate a packet length statistic, valid at the end of every
//		packet. It's a summary statistic of every packet.  The summary
//	consists of { ABORT, OVERFLOW, packet_length_in_bytes }.  ABORT will
//	be true if the packet is ever aborted.  OVERFLOW will be true if the
//	count overflowed.  Otherwise, packet_length_in_bytes will contain the
//	number of bytes in the received packet.  M_VALID will be set at the
//	end of any active packet--whether aborted or concluded.  These stats
//	may then to be used when debugging the netpath.v.
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
module	pktcount #(
		// {{{
		localparam	PKTDW = 64,
		parameter	LGPKTLN = 16,
		localparam	PKTLSB = $clog2(PKTDW/8)
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Incoming packets to measure
		// {{{
		input	wire			S_VALID,
		// output wire			S_READY,
		// input wire	[PKTDW-1:0]		S_DATA,
		input	wire	[PKTLSB-1:0]	S_BYTES,
		input	wire			S_LAST,
		input	wire			S_ABORT,
		// }}}
		// Outgoing received packets
		// {{{
		output	reg				M_VALID,
		input	wire				M_READY,
		output	reg	[LGPKTLN+2-1:0]		M_DATA
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg				active;
	reg	[LGPKTLN-PKTLSB:0]	word_count;
	// }}}

	always @(posedge i_clk)
	if (i_reset)
	begin
		active <= 0;
		word_count <= 0;
	end else if (S_ABORT)
	begin
		active <= 0;
		word_count <= 0;
	end else if (S_VALID)
	begin
		active <= 1;
		if (!word_count[LGPKTLN-PKTLSB])
			word_count <= word_count + 1;
		if (S_LAST)
		begin
			active <= 0;
			word_count <= 0;
		end
	end

	always @(posedge i_clk)
	if (i_reset)
		M_VALID <= 0;
	else if ((S_ABORT && active) || (S_VALID && S_LAST))
	begin
		M_VALID <= (!S_ABORT || active);
	end else if (M_READY)
		M_VALID <= 0;

	initial	M_DATA = 0;
	always @(posedge i_clk)
	if((!M_VALID || M_READY)&&((S_ABORT && active) || (S_VALID && S_LAST)))
	begin
		M_DATA <= 0;
		if (word_count[LGPKTLN-PKTLSB]
					|| (S_BYTES == 0 && (&word_count)))
			M_DATA <= { S_ABORT, 1'b1, {(LGPKTLN){1'b0}} };
		else if (S_BYTES == 0)
			M_DATA <= { S_ABORT, word_count, {(PKTLSB){1'b0}} }
				+ (1 << PKTLSB);
		else
			M_DATA <= { S_ABORT, word_count, S_BYTES };
	end

	// Keep Verilator happy
	// {{{
	// Verilator lint_on  UNUSED
	// Verilator coverage_off
	wire	unused;
	assign	unused =  &{ 1'b0 };
	// Verilator coverage_on
	// Verialtor lint_off UNUSED
	// }}}
endmodule
