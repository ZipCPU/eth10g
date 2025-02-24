////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/hdmibchdec.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Decode the BCH encoded words encoding an (otherwise) 32b packet.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024-2025, Gisselquist Technology, LLC
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
`default_nettype	none
// }}}
module	hdmibchdec (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire		S_VALID,
		input	wire		S_HDR,
		input	wire	[7:0]	S_DATA,
		input	wire		S_LAST,
		//
		output	wire		M_VALID,
		output	wire	[7:0]	M_DATA,
		output	wire		M_LAST
		//
		// output	wire	[7:0]	o_dbg
		// }}}
	);

	// Local declarations
	// {{{
	reg	[23:0]	dec32	[0:255];
	reg	[55:0]	dec64	[0:255];
	reg	[7:0]	hfill, b0fill, b1fill, b2fill, b3fill;
	reg	[32:0]	hdrsr;
	reg	[35:0]	bsreg, d0sr, d1sr, d2sr, d3sr, d4sr, d5sr, d6sr,
			d7sr, lastsr;
	reg	[4:0]	pkt_count;
	reg		zero_pkt;

	reg		r_valid, r_last;
	reg	[7:0]	r_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate the BCH decode table
	// {{{
`ifdef	GENCODE
	reg	[63:0]	tmpdata;
	reg	[7:0]	tmpsynd;
	integer	ij, ik, ip;

	initial begin
		// 64b Dual error correction (to extent possible)
		// {{{
		// Should this instead be decoding to a failure, and thus an
		// ABORT?
		for(ij=0; ij<63; ij=ij+1)
		begin
			for(ik=ij+1; ik<64; ik=ik+1)
			begin
				tmpdata = 0;
				tmpdata[ij] = 1;
				tmpdata[ik] = 1;
				tmpsynd = 8'h0;
				for(ip=0; ip<64; ip=ip+1)
					tmpsynd =ECCFN(tmpsynd, tmpdata[63-ip]);

				tmpdata = 0;
				tmpdata[ij] = 1;
				tmpdata[ik] = 1;

				dec64[tmpsynd] = tmpdata[63:8];
			end
		end
		// }}}

		// 64b Single error correction
		// {{{
		for(ij=0; ij<64; ij=ij+1)
		begin
			tmpdata = 0;
			tmpdata[ij] = 1;
			tmpsynd = 8'h0;
			for(ip=0; ip<64; ip=ip+1)
				tmpsynd =ECCFN(tmpsynd, tmpdata[63-ip]);

			tmpdata = 0;
			tmpdata[ij] = 1;

			dec64[tmpsynd] = tmpdata[63:8];
		end
		// }}}

		// Zero errors always decodes to zero corrections
		dec64[8'h0] = 56'h0;


		// 32b Dual error correction (to extent possible)
		// {{{
		// Should this be a failure instead?
		for(ij=0; ij<31; ij=ij+1)
		begin
			for(ik=ij+1; ik<32; ik=ik+1)
			begin
				tmpdata = 0;
				tmpdata[ij] = 1;
				tmpdata[ik] = 1;
				tmpsynd = 8'h0;
				for(ip=0; ip<32; ip=ip+1)
					tmpsynd =ECCFN(tmpsynd, tmpdata[31-ip]);

				tmpdata = 0;
				tmpdata[ij] = 1;
				tmpdata[ik] = 1;

				dec32[tmpsynd] = tmpdata[31:8];
			end
		end
		// }}}

		// 32b Single error correction
		// {{{
		for(ij=0; ij<32; ij=ij+1)
		begin
			tmpdata = 0;
			tmpdata[ij] = 1;
			tmpsynd = 8'h0;
			for(ip=0; ip<32; ip=ip+1)
				tmpsynd =ECCFN(tmpsynd, tmpdata[31-ip]);

			tmpdata = 0;
			tmpdata[ij] = 1;

			dec32[tmpsynd] = tmpdata[31:8];
		end
		// }}}

		// 32b zero errors -> zero corrections
		dec32[8'h0] = 24'h0;
	end
`else
	initial	$readmemh("bchdec64.hex",dec64);
	initial	$readmemh("bchdec32.hex",dec32);
`endif
	// }}}

	// reg	[39:0]	dbg_syndrome;

	// DATA/HDR shift registers
	// {{{
	always @(posedge i_clk)
	begin
		hdrsr  <= { hdrsr[31:0], S_VALID && S_HDR  };
		bsreg  <= { bsreg[34:0], S_VALID };
		d0sr   <= { d0sr[34:0], S_VALID && S_DATA[0] };
		d1sr   <= { d1sr[34:0], S_VALID && S_DATA[1] };
		d2sr   <= { d2sr[34:0], S_VALID && S_DATA[2] };
		d3sr   <= { d3sr[34:0], S_VALID && S_DATA[3] };
		d4sr   <= { d4sr[34:0], S_VALID && S_DATA[4] };
		d5sr   <= { d5sr[34:0], S_VALID && S_DATA[5] };
		d6sr   <= { d6sr[34:0], S_VALID && S_DATA[6] };
		d7sr   <= { d7sr[34:0], S_VALID && S_DATA[7] };
		lastsr <= { lastsr[34:0], S_VALID && S_LAST };

		zero_pkt <= zero_pkt && (!S_VALID || S_DATA == 8'h0);
		// dbg_syndrome <= { d3sr[34], d2sr[34], d1sr[34], d0sr[34],
		//		lastsr[8:5], dbg_syndrome[39:8] };

		if (lastsr[0])
		begin
			zero_pkt <= !S_VALID || S_DATA == 8'h0;
			hdrsr[32:9] <= hdrsr[31:8] ^ dec32[hfill];
			{ d0sr[32:5], d4sr[32:5] } <= DECODE(
					{ d0sr[31:4], d4sr[31:4] }, b0fill);
			{ d1sr[32:5], d5sr[32:5] } <= DECODE(
					{ d1sr[31:4], d5sr[31:4] }, b1fill);
			{ d2sr[32:5], d6sr[32:5] } <= DECODE(
					{ d2sr[31:4], d6sr[31:4] }, b2fill);
			{ d3sr[32:5], d7sr[32:5] } <= DECODE(
					{ d3sr[31:4], d7sr[31:4] }, b3fill);

			lastsr[5] <= 1'b1;
			bsreg[ 4:1] <= 4'h0;
			lastsr[4:1] <= 4'h0;

			// dbg_syndrome <= { b3fill, b2fill, b1fill, b0fill, hfill };
		end

		if (!S_VALID || S_LAST)
			pkt_count <= 0;
		else
			pkt_count <= pkt_count + 1;

		if ((!S_VALID && pkt_count != 0)
				||(S_VALID && S_LAST
					&& ((zero_pkt && S_DATA == 8'h0)
						|| pkt_count[4:0] != 5'd31)))
		begin
			lastsr[0] <= 1'b0;
			pkt_count <= 0;
			case(pkt_count[4:0])
			5'h00: bsreg[ 0:0] <= 0;
			5'h01: bsreg[ 1:0] <= 0;
			5'h02: bsreg[ 2:0] <= 0;
			5'h03: bsreg[ 3:0] <= 0;
			5'h04: bsreg[ 4:0] <= 0;
			5'h05: bsreg[ 5:0] <= 0;
			5'h06: bsreg[ 6:0] <= 0;
			5'h07: bsreg[ 7:0] <= 0;
			5'h08: bsreg[ 8:0] <= 0;
			5'h09: bsreg[ 9:0] <= 0;
			5'h0a: bsreg[10:0] <= 0;
			5'h0b: bsreg[11:0] <= 0;
			5'h0c: bsreg[12:0] <= 0;
			5'h0d: bsreg[13:0] <= 0;
			5'h0e: bsreg[14:0] <= 0;
			5'h0f: bsreg[15:0] <= 0;
			5'h10: bsreg[16:0] <= 0;
			5'h11: bsreg[17:0] <= 0;
			5'h12: bsreg[18:0] <= 0;
			5'h13: bsreg[19:0] <= 0;
			5'h14: bsreg[20:0] <= 0;
			5'h15: bsreg[21:0] <= 0;
			5'h16: bsreg[22:0] <= 0;
			5'h17: bsreg[23:0] <= 0;
			5'h18: bsreg[24:0] <= 0;
			5'h19: bsreg[25:0] <= 0;
			5'h1a: bsreg[26:0] <= 0;
			5'h1b: bsreg[27:0] <= 0;
			5'h1c: bsreg[28:0] <= 0;
			5'h1d: bsreg[29:0] <= 0;
			5'h1e: bsreg[30:0] <= 0;
			5'h1f: bsreg[31:0] <= 0;
			endcase
		end

		if (i_reset)
		begin
			zero_pkt <= 1;
			lastsr <= 0;
			pkt_count <= 0;
			bsreg <= 0;
		end
	end
	// }}}

	// assign	o_dbg = dbg_syndrome[7:0];

	// ECC parity fill/syndrome register(s)
	// {{{
	always @(posedge i_clk)
	if (S_VALID)	// && S_READY is implied
	begin
		if (S_LAST && pkt_count[4:0] != 5'd31)
		begin
			hfill  <= 0;
			b0fill <= 0;
			b1fill <= 0;
			b2fill <= 0;
			b3fill <= 0;
		end else if (lastsr[0])
		begin
			hfill  <= ECCFN(hfill, S_HDR);
			b0fill <= ECCFN(ECCFN(8'h00, S_DATA[0]), S_DATA[4]);
			b1fill <= ECCFN(ECCFN(8'h00, S_DATA[1]), S_DATA[5]);
			b2fill <= ECCFN(ECCFN(8'h00, S_DATA[2]), S_DATA[6]);
			b3fill <= ECCFN(ECCFN(8'h00, S_DATA[3]), S_DATA[7]);
		end else begin
			hfill  <= ECCFN(hfill, S_HDR);
			b0fill <= ECCFN(ECCFN(b0fill, S_DATA[0]), S_DATA[4]);
			b1fill <= ECCFN(ECCFN(b1fill, S_DATA[1]), S_DATA[5]);
			b2fill <= ECCFN(ECCFN(b2fill, S_DATA[2]), S_DATA[6]);
			b3fill <= ECCFN(ECCFN(b3fill, S_DATA[3]), S_DATA[7]);
		end
	end else begin
		hfill  <= 0;
		b0fill <= 0;
		b1fill <= 0;
		b2fill <= 0;
		b3fill <= 0;
	end
	// }}}

	always @(posedge i_clk)
	if (i_reset)
		r_valid <= 1'b0;
	else
		r_valid <= (|lastsr[7:5]) || bsreg[35];

	always @(posedge i_clk)
	if (lastsr[5])
		r_data <= hdrsr[32:25];
	else if (lastsr[6])
		r_data <= hdrsr[25:18];
	else if (lastsr[7])
		r_data <= hdrsr[18:11];
	else
		r_data <= { d7sr[35], d6sr[35], d5sr[35], d4sr[35],
				d3sr[35], d2sr[35], d1sr[35], d0sr[35] };

	always @(posedge i_clk)
		r_last <= lastsr[35];

	assign	M_VALID = r_valid;
	assign	M_DATA  = r_data;
	assign	M_LAST  = r_last;

	localparam	[7:0]	ECCPOLY = 8'hc1;

	function [7:0]	ECCFN(input [7:0] fill, input b);
	// {{{
	begin
		if (b ^ fill[7])
			ECCFN = { fill[6:0], 1'b0 } ^ ECCPOLY;
		else
			ECCFN = { fill[6:0], 1'b0 };
	end endfunction
	// }}}

	function automatic [55:0] DECODE(input [55:0] dat, input [7:0] synd);
		// {{{
		reg	[55:0]	vec;
	begin
`ifdef	GENCODE
		integer	i;
		reg	[55:0]	ivec, ovec;

		ivec = 0;
		for(i=0; i<28; i=i+1)
		begin
			ivec[2*i+1] = dat[55-i];
			ivec[2*i  ] = dat[27-i];
		end

		vec = ivec ^ dec64[synd];

		ovec = 0;
		for(i=0; i<28; i=i+1)
		begin
			ovec[55-i] = vec[2*i+1];
			ovec[27-i] = vec[2*i  ];
		end

		DECODE = ovec;
`else
		vec = dat ^ dec64[synd];
		DECODE = vec;
`endif
	end endfunction
	// }}}
endmodule
