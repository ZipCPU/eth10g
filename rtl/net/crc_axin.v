////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	crc_axin.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Checks incoming packets for valid CRCs.  Any incoming packet
//		arriving with a bad CRC should be ABORTed on or before the LAST
//	signal--in this case, concurrent with the LAST signal.  (The ABORT
//	signal will need to be raised coincident with the final outgoing LAST
//	signal, so subsequent components know not to store the packet into
//	memory, or to forward it through the network.)
//
// Algorithm notes:
//	Since we don't know which byte will end a packet, we have to calculate
//	the appropriate CRC for all possible packet endings.  Sadly, the
//	traditional CRC algorithm (compute CRC for ending #1, ending #2 is
//	then calculated from ending #1 and a new byte, ending #3 is calculated
//	from ending #2 and a second new byte, etc.) doesn't meet timing.  Hence,
//	the algorithm has been modified so that each bit of the CRC is
//	calculated from a linear equation instead.  That way, we can calculate
//	each CRC bit (b), for each of the 32bits composing a CRC, for each
//	potential ending byte (B) all using the same equation:
//
//	(Let's let k = 32*B+b)
//	for(k=0; k<32*DATA_WIDTH/8; k=k+1)
//	if (S_AXIN_VALID && S_AXIN_READY)
//		crc[k] = ^(EQUATION[k] & { new_input_word, crc })
//
//	For a DATA_WIDTH of 64b, EQUATION[k] will have (typically and roughly)
//	(DATA_WIDTH/8 + CRC_WIDTH/2 = 32+16 =) 48 bits active.  These 48 bits
//	can then be placed into 8 LUT6s, the output of these 8 LUT6s can then
//	be fed into two LUT6s (with carry) to finish the logic.  Hence:
//	32*(64/8)*(8+2) = 32*8*10 = 2560 LUTs.  In practice, Yosys can build
//	this entire module in 2,305 LUTs (including merging less than fully
//	utilized LUTs), so its not quite so bad.
//
// Creator:	Sukru Uzun.
//	    	Gisselquist Technology, LLC
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
`default_nettype none
// }}}
module	crc_axin #(
		// {{{
		parameter	    DATA_WIDTH = 64,
		parameter [0:0]	OPT_SKIDBUFFER = 1'b0,
		parameter [0:0]	OPT_LOWPOWER   = 1'b0,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b1
		// }}}
	) (
		// {{{
		// clk and low reset
		input	wire	        ACLK, ARESETN,
		// calculate crc if enable
		input   wire            i_cfg_en,

		// S_AXIN_*: Incoming data
		// {{{
		input	wire			S_AXIN_VALID,
		output  wire			S_AXIN_READY,
		input	wire [DATA_WIDTH-1:0]	S_AXIN_DATA,
		// Byte counter
		input   wire [$clog2(DATA_WIDTH/8):0]	S_AXIN_BYTES,
		// Indicates boundary of last packet
		input	wire			S_AXIN_LAST,
	        input	wire			S_AXIN_ABORT,
		// }}}

		// M_AXIN_*: Outgoing data
		output	reg				M_AXIN_VALID,
		input   wire				M_AXIN_READY,
		output	reg	[DATA_WIDTH-1:0]	M_AXIN_DATA,
		output  reg [$clog2(DATA_WIDTH/8):0]	M_AXIN_BYTES,
		// Indicates boundary of last packet
		output	reg 				M_AXIN_LAST,
		output	reg 				M_AXIN_ABORT
		// }}}
	);

	// Local declarations
	// {{{
	localparam					DW = DATA_WIDTH;
	localparam					CRC_BITS = 32;
	localparam	[CRC_BITS-1:0]	POLY = 32'hedb88320; // 04C11DB7;
	localparam	[CRC_BITS-1:0]	INIT = 32'hFFFFFFFF;
	localparam	[CRC_BITS-1:0]	XOR_OUT = 32'hFFFFFFFF;
	localparam					INDEX_OFFSET = (DW - CRC_BITS)/8;

	reg				i_cfg_en_reg;
	reg				m_valid_reg;
	reg	[DATA_WIDTH-1:0]	m_data_reg;
	reg [$clog2(DATA_WIDTH/8):0]	m_bytes_reg;
	reg 			m_last_reg;
	reg 			skd_last_reg, skd_valid_reg, skd_ready_reg;

	genvar	gk;

	// All declarations go at the top ...
	reg	[CRC_BITS-1:0]	crc32		[0:(DW/8)-1];
	wire [CRC_BITS*(DW/8)-1:0]	next_crc_wide;

	wire					skd_valid, skd_ready,
							skd_last, skd_abort;
	wire [DW-1:0]			skd_data;
	wire [$clog2(DW/8):0]	skd_bytes;

	wire [$clog2(DW/8):0]	crc_index;
	reg [CRC_BITS-1:0]		crc_value;
	reg	 [DW-1:0]			last_axin_data;
	wire [2*DW-1:0]			wide_word;
	reg [2*DW-1:0]			end_word;

	// }}}

	// swap endianness
	function [DW-1:0] SWAP_ENDIANNESS(input [DW-1:0] data);
	// {{{
		integer			s;
		reg	[DW-1:0]	tmp;
	begin
		if(OPT_LITTLE_ENDIAN)
			SWAP_ENDIANNESS = data;
		else begin
			tmp = 0;
			for(s=0; s<DW/8; s=s+1)
			begin
				tmp[s * 8 +: 8] = data[(DW/8-s-1) +: 8];
			end
			SWAP_ENDIANNESS = tmp;
		end
	end endfunction
	// }}}

	// crc32 -- update our (current) CRC values
	crc_eqn #(
		.DW(DW),
		.CRC_BITS(CRC_BITS),
		.POLYNOMIAL(POLY)
	) crc_eq (
		.skd_data(skd_data),
		.crc32(crc32[DW/8 - 1]),
		.next_crc_wide(next_crc_wide)
	);

	// (Optional) skidbuffer
	// {{{
	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER
		netskid #(
			.DW(DW+$clog2(DW/8)+1)
		) u_skidbuffer (
			// {{{
			.i_clk(ACLK), .i_reset(!ARESETN),

			.S_AXIN_VALID(S_AXIN_VALID),
			.S_AXIN_READY(S_AXIN_READY),
			.S_AXIN_DATA({ S_AXIN_BYTES,
					SWAP_ENDIANNESS(S_AXIN_DATA) }),
			.S_AXIN_LAST(S_AXIN_LAST),
			.S_AXIN_ABORT(S_AXIN_ABORT),

			.M_AXIN_VALID(skd_valid),
			.M_AXIN_READY(skd_ready),
			.M_AXIN_DATA({ skd_bytes, skd_data }),
			.M_AXIN_LAST(skd_last),
			.M_AXIN_ABORT(skd_abort)
			// }}}
		);

	end else begin : NO_SKIDBUFFER

		assign	skd_valid = S_AXIN_VALID;
		assign	S_AXIN_READY = skd_ready;
		assign	skd_data  = SWAP_ENDIANNESS(S_AXIN_DATA);
		assign	skd_bytes = S_AXIN_BYTES;
		assign	skd_last  = S_AXIN_LAST;
		assign	skd_abort = S_AXIN_ABORT;

	end endgenerate
	// }}}

	// skd_ready
	// {{{
	// 10Gb Ethernet
	// 312.5 MHz clock
	// This means S_AXIN_VALID && S_AXIN_READY must both be true for
	// many clock cycles in a row, or packets will be dropped.
	//
	assign	skd_ready = !M_AXIN_VALID || M_AXIN_READY || skd_abort;
	//
	// }}}

	// M_AXIN_VALID
	// {{{
	initial M_AXIN_VALID = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		m_valid_reg <= 0;
	else if (skd_valid && skd_ready && !skd_abort)
		m_valid_reg <= 1;
	else if (M_AXIN_READY)
		m_valid_reg <= 0;

	always @(posedge ACLK)
	if (!ARESETN)
		M_AXIN_VALID <= 1'b0;
	else
		M_AXIN_VALID <= m_valid_reg;
	// }}}

	// M_AXIN_DATA
	// {{{
	always @(posedge ACLK)
	if (!ARESETN)
		m_data_reg <= 0;
	else if (!m_valid_reg || M_AXIN_READY)
	begin
		m_data_reg <= SWAP_ENDIANNESS(skd_data);
		if (OPT_LOWPOWER && (!skd_valid || skd_abort))
			m_data_reg <= 0;
	end

	initial M_AXIN_DATA = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		M_AXIN_DATA <= 0;
	else
		M_AXIN_DATA <= m_data_reg;
	// }}}

	// M_AXIN_LAST
	// {{{
	initial M_AXIN_LAST = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		m_last_reg <= 0;
	else if (!m_valid_reg || M_AXIN_READY)
		m_last_reg <= skd_valid && skd_last && skd_ready;

	always @(posedge ACLK)
	if (!ARESETN)
		M_AXIN_LAST <= 1'b0;
	else
		M_AXIN_LAST <= m_last_reg;
	// }}}

	// M_AXIN_BYTES
	// {{{
	initial M_AXIN_BYTES = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		m_bytes_reg <= 0;
	else if (!m_valid_reg || M_AXIN_READY)
	begin
		m_bytes_reg <= skd_bytes;
		if (OPT_LOWPOWER && (!skd_valid || skd_abort))
			m_bytes_reg <= 0;
	end

	initial M_AXIN_BYTES = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		M_AXIN_BYTES <= 0;
	else
		M_AXIN_BYTES <= m_bytes_reg;
	// }}}

	generate for(gk=0; gk < DW/8; gk=gk+1)
	begin : GEN_CRC

		always @(posedge ACLK)
		if (!ARESETN)
			crc32[gk] <= INIT;
		else if ((skd_valid && skd_ready && S_AXIN_LAST) || S_AXIN_ABORT)	// reset crc value
			crc32[gk] <= INIT;
		else if (skd_valid && skd_ready)
			crc32[gk] <= next_crc_wide[CRC_BITS*gk +: CRC_BITS];

	end endgenerate
	// }}}

	// end_word
	// {{{
	always @(posedge ACLK)
	if (S_AXIN_VALID && S_AXIN_READY)
		last_axin_data <= skd_data;

	assign	wide_word = { skd_data, last_axin_data };
	assign crc_index = (skd_bytes - 1) + { 1'b0, INDEX_OFFSET[$clog2(DW/8)-1:0] };

	always @(posedge ACLK)
	begin
		end_word <= wide_word >> ((skd_bytes + INDEX_OFFSET[$clog2(DW/8):0]) * 8);
		i_cfg_en_reg <= i_cfg_en;
		skd_last_reg <= skd_last;
		skd_valid_reg <= skd_valid;
		skd_ready_reg <= skd_ready;
	end

	always @(posedge ACLK)
	if (skd_bytes <= CRC_BITS[$clog2(DW):$clog2(DW/8)])
		crc_value <= crc32[crc_index[$clog2(DW/8)-1:0]] ^ XOR_OUT;
	else
		crc_value <= next_crc_wide[crc_index[$clog2(DW/8)-1:0]*CRC_BITS +: CRC_BITS] ^ XOR_OUT;

	initial M_AXIN_ABORT = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		M_AXIN_ABORT <= 0;
	else if (skd_abort && (!M_AXIN_VALID || !M_AXIN_LAST))
	begin
		// Abort if the incoming signal aborts
		// This will likely happen if skd_abort drops mid-packet
		// But ... don't abort the packet once
		// M_AXIN_VALID && M_AXIN_LAST are set.
		M_AXIN_ABORT <= 1'b1;
	end else if (i_cfg_en_reg && skd_valid_reg && skd_ready_reg
							&& !M_AXIN_ABORT)
	begin
		if (skd_last_reg)	// Should we check M_AXIN_LAST
			M_AXIN_ABORT <= (crc_value != end_word[CRC_BITS-1:0]);
	end else if (M_AXIN_READY || !m_valid_reg)
		M_AXIN_ABORT <= 1'b0;
	// }}}

	// Keep Verilator -Wall happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire 	unused;
	assign	unused = &{ 1'b0, end_word[2*DW-1:CRC_BITS], crc_index[$clog2(DW/8)] };
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
	// }}}
//
// Formal properties
// {{{
//
`ifdef FORMAL
//	Verification
//	1. When using SBY, ...
//	  -- Only this file, faxin_slave, and faxin_master are needed
//		(initially)
//	  -- Data can be anything--it might have a good CRC, it might not
//	  -- This will find/fix any signaling errors, but do nothing for CRC
//		validation. (You have signaling errors still ...)
//
//	2. SBY step #2 ...
//	  -- You could use an external environment to generate a good CRC, and
//		then *prove* that M_AXIN_ABORT does not get set.
//	  -- You'd then need something to create a packet for you. addecrc
//		could help.
//	  - *ALTERNATIVELY* you could use rxecrc to process a packet side by
//		side with crc_axin.
//	     -- If rxecrc doesn't fail, then prove crc_axin doesn't fail either
//	     -- If rxecrc succeeds, then prove crc_axin succeeds as well
//
//	3. Simulation
//	  -- Could still use addecrc.  Would need to ...
//		1. Pick a random packet length
//			Be sure to pick one with all remainders mod 8
//			i.e. 64-bytes, 65bytes, 66, 67, but 68 would be a repeat
//		2. Randomly decide if you will (or won't) abort the packet
//		3. Use addecrc to generate a packet, 8'bits at a time
//		4. Combine those 8'bits to 32'bits, for crc_axin's input
//		5. Verify that crc_axin doesn't abort
//	  -- This would help to verify that the CRC works
//	  -- Would do nothing to verify signaling
//	  -- Depending on how set up, might or might not verify CRC failures
//		are properly flagged.
//
	// These parameters are only used when we do our formal proof
	parameter	F_MIN_LENGTH = (8*8)/DW;
	parameter	F_MAX_LENGTH = (512*8)/DW;
	localparam	LGMX = (F_MAX_LENGTH > 0) ? $clog2(F_MAX_LENGTH+1):1;

	reg	f_past_valid;
	(* anyconst *) reg f_no_abort, f_never_abort_slave;

	wire	F_SLAVE_ARESETN;
	reg	[LGMX-1:0] f_s_stream_word, f_m_stream_word;
	reg	[12-1:0]   f_s_packets_rcvd, f_m_packets_rcvd;

	initial	f_past_valid = 0;
	always @(posedge ACLK)
		f_past_valid = 1;

	always @(posedge ACLK)
	if (!f_past_valid)
		assume(!ARESETN);

	always @(posedge ACLK)
	if (f_never_abort_slave)
		assume(!S_AXIN_ABORT);

	////////////////////////////////////////////////////////////////////////
	// Slave stream properties
	////////////////////////////////////////////////////////////////////////

	// assign F_SLAVE_ARESETN = ARESETN || !M_AXIN_ABORT;

	faxin_slave #(
		.DATA_WIDTH(DATA_WIDTH),
		.MIN_LENGTH(F_MIN_LENGTH),
		.MAX_LENGTH(F_MAX_LENGTH),
		.WBITS($clog2(DATA_WIDTH/8)+1)
	) fslave (
		.S_AXI_ACLK(ACLK), .S_AXI_ARESETN(ARESETN),
		.S_AXIN_VALID(S_AXIN_VALID),
		.S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA(S_AXIN_DATA),
		.S_AXIN_BYTES(S_AXIN_BYTES),
		.S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		.f_stream_word(f_s_stream_word),
		.f_packets_rcvd(f_s_packets_rcvd)
	);

	// S_AXIN_BYTES
	// {{{
	always @(*)
	if (ARESETN && S_AXIN_VALID)
	begin
		assume(S_AXIN_BYTES > 0);
		assume(S_AXIN_BYTES <= (DW/8));
		if (!S_AXIN_LAST)
			assume(S_AXIN_BYTES == (DW/8));
	end
	// }}}

	// F_MIN_LENGTH & S_AXIN_LAST
	// {{{
	always @(*)
	if (f_s_stream_word < F_MIN_LENGTH)
		assume(!S_AXIN_LAST);
	// }}}

	always @(*)
	if (f_no_abort)
	begin
		assume(!S_AXIN_ABORT && !i_cfg_en);
	end

	////////////////////////////////////////////////////////////////////////
	// Master stream properties
	////////////////////////////////////////////////////////////////////////

	faxin_master #(
		.DATA_WIDTH(DATA_WIDTH),
		.MIN_LENGTH(F_MIN_LENGTH),
		.MAX_LENGTH(F_MAX_LENGTH),
		.WBITS($clog2(DATA_WIDTH/8)+1)
	) fmaster (
		.S_AXI_ACLK(ACLK), .S_AXI_ARESETN(ARESETN),
		.S_AXIN_VALID(M_AXIN_VALID),
		.S_AXIN_READY(M_AXIN_READY),
		.S_AXIN_DATA(M_AXIN_DATA),
		.S_AXIN_BYTES(M_AXIN_BYTES),
		.S_AXIN_LAST(M_AXIN_LAST),
		.S_AXIN_ABORT(M_AXIN_ABORT),
		.f_stream_word(f_m_stream_word),
		.f_packets_rcvd(f_m_packets_rcvd)
	);

	// M_AXIN_BYTES
	// {{{
	always @(*)
	if (M_AXIN_VALID)
	begin
		assert(M_AXIN_BYTES > 0);
		assert(M_AXIN_BYTES <= DW/8);
		if (!M_AXIN_LAST)
			assert(M_AXIN_BYTES == DW/8);
	end
	// }}}

	integer i;
	always @(posedge ACLK)
	if (ARESETN)
	begin
		if (M_AXIN_VALID && M_AXIN_LAST)
		begin
			for(i=0; i < DW/8; i=i+1)
			begin
				assert(crc32[i] == INIT);
			end
		end
	end

	always @(*)
	begin
		if (f_never_abort_slave)
			assert((M_AXIN_VALID && M_AXIN_LAST) || !M_AXIN_ABORT);
		if (f_no_abort)
			assert(!M_AXIN_ABORT);
	end

	always @(*)
	if (ARESETN)
	begin
		if (f_s_stream_word == 0)
			assert ((!M_AXIN_VALID && f_m_stream_word == 0) || (M_AXIN_VALID && M_AXIN_LAST) || M_AXIN_ABORT);
		if (f_s_stream_word != 0 && !M_AXIN_ABORT)
		begin
			assert(f_s_stream_word == f_m_stream_word + (M_AXIN_VALID ? 1 : 0));
		end
		if (M_AXIN_ABORT || M_AXIN_LAST)
			assert((f_s_stream_word == 0) || S_AXIN_ABORT);
		if (M_AXIN_VALID && M_AXIN_LAST)
		begin
			assert(f_s_stream_word == 0);
		end
	end

	// Cover
	// {{{
	always @(*)
	begin
		cover(f_never_abort_slave && M_AXIN_VALID && M_AXIN_LAST && !M_AXIN_ABORT);
		cover(f_never_abort_slave && M_AXIN_VALID && M_AXIN_LAST && M_AXIN_ABORT);
		cover(f_never_abort_slave && M_AXIN_VALID && M_AXIN_LAST && f_m_stream_word == 16);
	end
	// }}}

	// "Careless" assumptions
	// {{{
	// always @(*)
		// assume(!S_AXIN_ABORT);
	// }}}

`endif
// }}}
endmodule
