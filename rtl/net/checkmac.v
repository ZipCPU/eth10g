////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	checkmac.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	checkmac is an incoming packet processor, operating on AXI
//		network packet streams (i.e. abortable packet streams).  It
//	acts as a bump in a processing chain, with a twofold purpose:
//	1) Abort any incoming packets that aren't address to my MAC, 2) with
//	the exception of any broadcast ARP packets that are addressed to my
//	IPv4 address.
//
//	This means ...
//		If bits [PKTDW-1:PKTDW-48] are not my MAC,
//			and (not broadcast address,
//				or EthType != 0x0806 (ARP)
//				or payload bytes 24-27 != MY_IP)
//			and (not broadcast address,
//				or EthType != 0x86dd (IPv6)
//				or NDPType != 135 (Neighbor solicitation)
//				or ... I can't find all the details, so or true)
//		THEN drop the packet
//
//	The packet might still not be for the CPU, but at least the CPU can
//	take care of it from there on out.
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
module	checkmac #(
		// {{{
		parameter [47:0]	THIS_MAC  = 48'h0,
		// parameter [31:0]	THIS_IPV4 = 32'h0,
		parameter [15:0]	ARP_ETHERTYPE = 16'h0806,
		parameter		PKTDW = 128,
		parameter [0:0]		OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire				S_VALID,
		output	wire				S_READY,
		input	wire	[PKTDW-1:0]		S_DATA,
		input	wire	[$clog2(PKTDW/8)-1:0]	S_BYTES,
		input	wire				S_LAST, S_ABORT,
		//
		output	reg				M_VALID,
		input	wire				M_READY,
		output	reg	[PKTDW-1:0]		M_DATA,
		output	reg	[$clog2(PKTDW/8)-1:0]	M_BYTES,
		output	reg				M_LAST, M_ABORT
		// }}}
	);

	localparam [47:0]	BROADCAST_MAC = 48'hffff_ffff_ffff;

	generate if (PKTDW >= 128)
	begin : GEN_WIDEPKT
		reg		aborting, midpkt, initial_match;

		always @(*)
		begin
			if (S_DATA[PKTDW-1:PKTDW-48] == THIS_MAC)
				initial_match = 1'b1;
			else if (S_DATA[PKTDW-1:PKTDW-48] == BROADCAST_MAC
				&& S_DATA[PKTDW-2*48-1:PKTDW-2*48-16]==ARP_ETHERTYPE)
				initial_match = 1'b1;
			else
				initial_match = 1'b0;

			if (midpkt)
				initial_match = 1'b0;
		end

		always @(posedge i_clk)
		if (i_reset)
			midpkt <= 1'b0;
		else if (S_ABORT && (!S_VALID || S_READY))
			midpkt <= 1'b0;
		else if (S_VALID && S_READY)
			midpkt <= !S_LAST;

		always @(posedge i_clk)
		if (i_reset)
			M_VALID <= 1'b0;
		else if (S_VALID && S_READY && !aborting)
			M_VALID <= S_VALID && !S_ABORT
						&& (midpkt || initial_match);
		else if (M_READY)
			M_VALID <= 1'b0;

		always @(posedge i_clk)
		if (S_VALID && S_READY && (!OPT_LOWPOWER || !aborting))
		begin
			M_BYTES <= S_BYTES;
			M_DATA  <= S_DATA;
			M_LAST  <= S_LAST;
		end

		always @(posedge i_clk)
		if (i_reset)
			aborting <= 1'b0;
		else if (S_ABORT && (!S_VALID || S_READY))
			aborting <= 1'b0;
		else if (S_VALID && S_READY && S_LAST)
			aborting <= 1'b0;
		else if (S_VALID && S_READY && !midpkt && !initial_match)
			aborting <= 1'b1;

		always @(posedge i_clk)
		if (i_reset)
			M_ABORT <= 1'b0;
		else if (M_ABORT && (!M_VALID || M_READY))
			M_ABORT <= 1'b0;
		else if (S_ABORT && (!S_VALID || S_READY) &&midpkt && !aborting)
			M_ABORT <= 1'b1;

		assign	S_READY = (!M_VALID || M_READY || aborting);
	end // else if other packet widths ...
	endgenerate
endmodule
