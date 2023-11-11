////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/routetbl.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is intended to be the core of the network router: the
//		routing table.  When a packet is received, from any interface,
//	it is registered in this table together with the interface it comes
//	from.  Then, when we later want to transmit a packet, the table can be
//	queried for which port the given MAC address was last seen on.
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
module routetbl #(
		// {{{
		// parameter [0:0]	OPT_SKIDBUFFER   = 1'b0,
		// parameter [0:0]	OPT_LOWPOWER     = 1'b0
		// parameter [0:0]	OPT_DEFBROADCAST = 1'b0
		// parameter [0:0]	OPT_ONE_TO_MANY  = 1'b0
		parameter	NETH = 4,	// Number of incoming eth ports
		parameter [NETH-1:0]	OPT_ALWAYS = {(NETH){1'b0}},
		parameter [NETH-1:0]	OPT_NEVER  = {(NETH){1'b0}},
		parameter  [NETH-1:0]	BROADCAST_PORT = {(NETH){1'b1}} & (~OPT_NEVER),
		parameter  [NETH-1:0]	DEFAULT_PORT = BROADCAST_PORT & (~OPT_NEVER),
		parameter	LGTBL = 6,	// Log_2(NTBL entries)
		parameter	MACW = 48,	// Bits in a MAC address
		parameter	LGTIMEOUT = 24,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		localparam	NTBL = (1<<LGTBL) // Number of table entries
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Incoming packet header data from all interfaces
		// {{{
		input	wire	[NETH-1:0]		RX_VALID,
		output	wire	[NETH-1:0]		RX_READY,
		input	wire	[NETH*MACW-1:0]		RX_SRCMAC,
		// }}}
		// Outgoing packet data, needing destination lookup
		// {{{
		input	wire				TX_VALID,
		output	reg				TX_ACK,
		input	wire	[MACW-1:0]		TX_DSTMAC,
		output	reg	[NETH-1:0]		TX_PORT,
		// }}}
		// A quick and dirty debugging interface
		// {{{
		output	reg	[$clog2(NETH)-1:0]	o_dbg_insert_port,
		output	reg	[MACW-1:0]		o_dbg_insert_srcmac,
		output	reg	[NETH-1:0]		o_dbg_lookup_port,
		output	reg	[MACW-1:0]		o_dbg_lookup_dstmac,
		output	reg	[LGTBL:0]		o_dbg_fill
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam	LGETH = $clog2(NETH);
	integer	ik;
	genvar	gk, galt;

	wire	[NETH-1:0]	rxgrant;
	wire			rxarb_valid;
	wire			rxarb_ready;
	reg	[MACW-1:0]	rxarb_srcmac;
	reg	[LGETH-1:0]	rxarb_port;

	reg	[NTBL-1:0]		tbl_valid;
	reg	[NTBL-1:0]		prematch, oldest;
	wire	[NTBL-1:0]		tbl_write;
	reg	[LGTIMEOUT-1:0]		tbl_age		[NTBL-1:0];
	reg	[LGETH-1:0]		tbl_port	[NTBL-1:0];
	reg	[MACW-1:0]		tbl_mac		[NTBL-1:0];
	wire				tbl_full;
`ifdef	FORMAL
	wire	[NTBL-1:0]		tbl_older	[NTBL-1:0];
`endif

	wire	[NTBL-1:0]	lkup_tblmatch;
	reg	[NETH-1:0]	lkup_port;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Arbitrate among inputs
	// {{{
	pktarbiter #(
		.W(NETH)
	) u_arbiter (
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.i_req(RX_VALID & (~OPT_NEVER)), .i_stall(!rxarb_ready),
		.o_grant(rxgrant)
	);

	assign	rxarb_valid = |(RX_VALID & rxgrant);
	assign	RX_READY    = OPT_NEVER | (rxarb_ready ? rxgrant : 0);

	assign	rxarb_ready = 1;

	always @(*)
	begin
		rxarb_port = 0;
		for(ik=0; ik<NETH; ik=ik+1)
		if (rxgrant[ik] && (!OPT_NEVER[ik]))
			rxarb_port = rxarb_port | ik[LGETH-1:0];
	end

	always @(*)
	begin
		rxarb_srcmac = 0;
		for(ik=0; ik<NETH; ik=ik+1)
		if (rxgrant[ik] && (!OPT_NEVER[ik]))
			rxarb_srcmac = rxarb_srcmac
					| RX_SRCMAC[ik * MACW +: MACW];
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Log incoming packets into our table
	// {{{

	assign	tbl_full = (&tbl_valid);
	generate for(gk=0; gk<NTBL; gk=gk+1)
	begin : GEN_PER_TBLENTRY
		wire			first_invalid;
		wire	[NTBL-1:0]	is_older;

		always @(*)
			prematch[gk] = tbl_valid[gk] && rxarb_valid
				&& tbl_mac[gk] == rxarb_srcmac;

		if (gk == 0)
		begin : GEN_MY_INVALID
			assign	first_invalid = !tbl_valid[gk];
		end else begin : ACC_INVALID
			assign	first_invalid = !tbl_valid[gk]
					&& (&tbl_valid[gk-1:0]);
		end

		// Find what's older
		for(galt=0; galt<NTBL; galt=galt + 1)
		begin
			if (galt == gk)
			begin : NOT_MY_ENTRY
				assign	is_older[galt] = 1'b0;
			end else begin : GEN_ISOLDER
				reg	r_is_older;

				// r_is_older == alt is older than me
				//	or equiv tbl_age[galt] < tbl_age[gk]
				//
				always @(posedge i_clk)
				if (i_reset)
					r_is_older <= 1'b0;
				else if (tbl_write[galt])
					r_is_older <= 1'b0; // !tbl_valid[gk];
				else if (tbl_write[gk])
					r_is_older <= tbl_valid[galt];

				assign	is_older[galt] = r_is_older;
`ifdef	FORMAL
				always @(*)
				if (!i_reset)
				begin
					if (tbl_valid[galt] && tbl_valid[gk])
						assert(r_is_older == (tbl_age[galt] < tbl_age[gk]));
					// if (!tbl_valid[galt] && !tbl_valid[gk])
					//	assert(!r_is_older);
				end
`endif
			end
		end

		// OLDEST: True if this element is the oldest in the table
		always @(*)
		if (!tbl_full)
		begin
			oldest[gk] = first_invalid;
		end else begin
			oldest[gk] = (is_older == 0);
		end

		assign	tbl_write[gk] = rxarb_valid && (prematch[gk]
					|| (prematch == 0 && oldest[gk]));

		always @(posedge i_clk)
		if (i_reset)
		begin
			tbl_valid[gk] <= 1'b0;
			tbl_age[gk]   <= 0;
		end else if (tbl_write[gk])
		begin
			tbl_valid[gk] <= 1'b1;
			tbl_age[gk]   <= {(LGTIMEOUT){1'b1}};
		end else if (tbl_valid[gk])
		begin
			tbl_valid[gk] <= (tbl_age[gk] > 1);
			tbl_age[gk]   <= tbl_age[gk] - 1;
		end

		always @(posedge i_clk)
		if (tbl_write[gk])
		begin
			tbl_mac[gk]  <= rxarb_srcmac;
			tbl_port[gk] <= rxarb_port;
		end
`ifdef	FORMAL
		assign	tbl_older[gk] = is_older;
		always @(*)
		if (!i_reset)
			assert(tbl_valid[gk] == (tbl_age[gk] != 0));
`endif
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Look up which request a transmit port should get sent to
	// {{{

	generate for(gk=0; gk<NTBL; gk=gk+1)
	begin

		assign	lkup_tblmatch[gk] = tbl_valid[gk]
				&& tbl_mac[gk] == TX_DSTMAC;
	end endgenerate

	always @(*)
	begin
		lkup_port = 0;
		for(ik=0; ik<NTBL; ik=ik+1)
		if (lkup_tblmatch[ik])
			lkup_port = lkup_port | (1<<tbl_port[ik]);
	end

	initial	TX_PORT = OPT_ALWAYS;
	always @(posedge i_clk)
	if (i_reset || (OPT_LOWPOWER && !TX_VALID))
		TX_PORT <= OPT_ALWAYS;
	else if (TX_VALID && !TX_ACK)
	begin
		if (&TX_DSTMAC)
			TX_PORT <= (BROADCAST_PORT & (~OPT_NEVER)) | OPT_ALWAYS;
		else if (lkup_tblmatch == 0)
			// No table lookup match.
			//
			// Non-matches can be broadcast
			TX_PORT <= (DEFAULT_PORT & (~OPT_NEVER)) | OPT_ALWAYS;
		else
			TX_PORT <= (lkup_port & (~OPT_NEVER)) | OPT_ALWAYS;
	end

	initial	TX_ACK = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		TX_ACK <= 1'b0;
	else
		TX_ACK <= TX_VALID && (!TX_ACK);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate some debug data
	// {{{

	always @(posedge i_clk)
	if (i_reset)
	begin
		o_dbg_insert_port   <= 0;
		o_dbg_insert_srcmac <= 0;
	end else if (|rxgrant)
	begin
		o_dbg_insert_port   <= rxarb_port;
		o_dbg_insert_srcmac <= rxarb_srcmac;
	end

	always @(posedge i_clk)
	if (i_reset)
	begin
		o_dbg_lookup_port   <= 0;
		o_dbg_lookup_dstmac <= 0;
	end else if (TX_VALID && TX_ACK)
	begin
		o_dbg_lookup_dstmac <= TX_DSTMAC;
		o_dbg_lookup_port   <= TX_PORT;
	end

	always @(posedge i_clk)
		o_dbg_fill <= COUNTONES(tbl_valid);

	function [LGTBL:0] COUNTONES(input [NTBL-1:0] ivalid);
		// {{{
		// Verilator lint_off BLKSEQ
		integer			ci;
		reg	[LGTBL:0]	count;
		// Verilator lint_on  BLKSEQ
	begin
		count = 0;
		for(ci=0; ci<NTBL; ci=ci+1)
		if (ivalid[ci])
			count = count+1;
		COUNTONES = count[LGTBL:0];
	end endfunction
	// }}}
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
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
	reg	f_past_valid;
	(* anyconst *)	reg	[LGETH-1:0]	fc_one, fc_two;
	(* anyconst *)	reg	[MACW-1:0]	fc_mac, fnvr_mac;
	(* anyconst *)	reg	[LGETH-1:0]	fc_port;
	wire			f_one_valid, f_two_valid;
	wire	[MACW-1:0]	f_one_mac,  f_two_mac;
	wire	[LGETH-1:0]	f_one_port, f_two_port;
	wire	[LGTIMEOUT-1:0]	f_one_age,  f_two_age;
	wire	[1:0]		f_oldest, f_prematch, f_write, f_match;
	reg	[NETH-1:0]	f_mask;
	wire	[NTBL-1:0]	f_one_older, f_two_older;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// RX stream source properties
	// {{{
	genvar	gfrx;

	generate for (gfrx=0; gfrx < NETH; gfrx = gfrx+1)
	begin : F_RXCHECK
		wire	[MACW-1:0]	port_mac;

		assign	port_mac = RX_SRCMAC[gfrx * MACW +: MACW];

		always @(posedge i_clk)
		if (!f_past_valid || $past(i_reset))
			assume(!RX_VALID[gfrx]);
		else if ($past(RX_VALID[gfrx] && !RX_READY[gfrx]))
		begin
			assume(RX_VALID[gfrx]);
			assume($stable(port_mac));
		end

		always @(*)
		if (RX_VALID[gfrx] && gfrx != fc_port)
			assume(port_mac != fc_mac);

		always @(*)
		if (RX_VALID[gfrx])
			assume(port_mac != fnvr_mac);
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Table lookup request properties
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assume(!TX_VALID);
		assert(!TX_ACK);
	end else if ($past(TX_VALID) && !$past(TX_ACK))
	begin
		assume(TX_VALID);
		assume($stable(TX_DSTMAC));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract
	// {{{

	// 1. No two table entries have the same MAC
	// 2. If two entries are valid, the most recent will not be marked
	//	as oldest
	// 3. Only one entry written to at a time
	// 4. If an entry is valid and not oldest, it will not be replaced
	// 5. Valid entries must have port numbers < NETH
	// 6. No two entries have the same age


	always @(*)
	begin
		assume(fc_one < fc_two);
		assume(fc_two < NETH);

		f_mask = (1<<fc_one) | (1<<fc_two);
	end

	assign	f_one_valid = tbl_valid[fc_one];
	assign	f_two_valid = tbl_valid[fc_two];

	assign	f_one_age   = tbl_age[fc_one];
	assign	f_two_age   = tbl_age[fc_two];

	assign	f_one_port  = tbl_port[fc_one];
	assign	f_two_port  = tbl_port[fc_two];

	assign	f_one_mac   = tbl_mac[fc_one];
	assign	f_two_mac   = tbl_mac[fc_two];

	assign	f_oldest   = { oldest[fc_two],    oldest[fc_one] };
	assign	f_prematch = { prematch[fc_two],  prematch[fc_one] };
	assign	f_write    = { tbl_write[fc_two], tbl_write[fc_one] };
	assign	f_match    = { lkup_tblmatch[fc_two], lkup_tblmatch[fc_one] };

	assign	f_one_older = tbl_older[fc_one];
	assign	f_two_older = tbl_older[fc_two];

	always @(*)
	if (f_past_valid)
	begin
		if (tbl_full)
			assert(f_one_valid && f_two_valid);
		if (f_one_valid && f_two_valid)
		begin
			assert(f_one_age != f_two_age);
			assert(f_one_mac != f_two_mac);

			if (f_one_age < f_two_age)
			begin
				assert(f_one_older[fc_two] == 1'b0);
				assert(f_two_older[fc_one] == 1'b1);
			end else begin
				assert(f_one_older[fc_two] == 1'b1);
				assert(f_two_older[fc_one] == 1'b0);
			end
		end

		if (f_one_valid && f_one_mac == fc_mac)
			assert(f_one_port == fc_port);
		if (f_one_valid)
			assert(f_one_mac != fnvr_mac);

		if (f_two_valid && f_two_mac == fc_mac)
			assert(f_two_port == fc_port);
		if (f_two_valid)
			assert(f_two_mac != fnvr_mac);

		// assert($onehot(oldest));
		// assert($onehot0(prematch));
		// assert($onehot0(tbl_write));

		assert($onehot0(f_prematch));
		assert($onehot0(f_write));
		assert(!f_oldest[1] || !f_oldest[0]);
		assert(!f_match[1]  || !f_match[0]);

		if (|f_write)
			assume((tbl_write & ~f_mask) == 0);
		else
			assume($onehot0(tbl_write));

		if (|f_oldest)
			assume((oldest & ~f_mask) == 0);
		else
			assume($onehot(oldest & ~f_mask));

		if (|f_prematch)
			assume((prematch & ~f_mask) == 0);
		else
			assume($onehot0(prematch));

		if (|f_match)
		begin
			assume((lkup_tblmatch & ~f_mask) == 0);
		end else begin
			assume($onehot0(lkup_tblmatch));
			if (TX_DSTMAC == fnvr_mac)
				assume((lkup_tblmatch & ~f_mask) == 0);
		end
	end

	always @(posedge i_clk)
	if (f_past_valid && !i_reset)
	begin
		if (rxarb_srcmac == fnvr_mac);
		begin
			assume((prematch & ~f_mask) == 0);
		end

		if(TX_VALID && TX_ACK)
		begin
			if (TX_DSTMAC == fnvr_mac)
				assert(TX_PORT == DEFAULT_PORT);

			if ($past(f_one_valid) && TX_DSTMAC == $past(f_one_mac)
							&& !(&TX_DSTMAC))
				assert(TX_PORT == (1<<$past(f_one_port)));

			if ($past(f_two_valid) && TX_DSTMAC == $past(f_two_mac)
							&& !(&TX_DSTMAC))
				assert(TX_PORT == (1<<$past(f_two_port)));
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	always @(posedge i_clk)
	if (!i_reset && $past(tbl_full))
	begin
		cover(tbl_full && TX_ACK);
		cover(tbl_full && TX_ACK && TX_PORT == 1);
		cover(TX_ACK && TX_PORT == DEFAULT_PORT);
		cover(TX_ACK && TX_PORT == {1'b1, {(NETH-1){1'b0}} });
		cover(TX_ACK && TX_PORT == BROADCAST_PORT);
		cover(TX_ACK && (&TX_DSTMAC));
	end

	always @(*)
	if (!i_reset)
		cover(TX_ACK && tbl_valid == 0 && TX_PORT == BROADCAST_PORT);
	// }}}
`endif
// }}}
endmodule
