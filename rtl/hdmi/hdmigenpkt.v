////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmi/hdmigenpkt.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:
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
module	hdmigenpkt (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire		S_VALID,
		output	wire		S_READY,
		input	wire	[7:0]	S_DATA,
		// Verilator lint_off UNUSED
		input	wire		S_LAST,
		// input wire		S_ABORT,
		// Verilator lint_on  UNUSED
		//
		output	wire		M_VALID,
		input	wire		M_READY,
		output	wire		M_HDR,
		output	wire	[7:0]	M_DATA,
		output	wire		M_LAST,
		//
		output	reg	[31:0]	o_debug
		// }}}
	);

	// Accept packet inputs -- must be 31 bytes each: 3 hdr octets, 28data
	// Local declarations
	// {{{
	localparam	IPKTLEN = 3+28;
	localparam	OPKTLEN = 32;
	localparam	LGFLEN = 5;
	reg	[5:0]		icount;
	reg	[LGFLEN:0]	loaded;
	wire	[LGFLEN:0]	fif_fill;
	wire			fif_full, fif_empty;

	reg			ivalid;
	wire			iready;
	reg	[8:0]		idata;
	reg			ilast;
	reg	[7:0]		b0fill, b1fill, b2fill, b3fill, hdrfill;
	reg	[30:0]		hdrsreg;
	// }}}

	assign	S_READY = (icount < IPKTLEN && (!ivalid || iready));

	// icount
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		icount <= 0;
	else if (S_VALID && S_READY)
	begin
		icount <= icount + 1;
		if (S_LAST ^ (icount == IPKTLEN-1))
			icount <= 0;
	end else if (icount >= IPKTLEN && iready)
	begin
		icount <= icount + 1;
		if (ilast) icount <= 0;
	end
	// }}}

	// hdrfill, hdrsreg, b?fill
	// {{{
	always @(posedge i_clk)
	if (S_VALID && S_READY)
	begin
		if (icount == 0)
		begin
			hdrfill <= ECCBYTE(8'h0, S_DATA);
			hdrsreg[30:23] <= S_DATA;
			ivalid <= 0;
		end else if (icount == 1)
		begin
			hdrfill <= ECCBYTE(hdrfill, S_DATA);
			hdrsreg[22:15] <= S_DATA;
			ivalid <= 0;
		end else if (icount == 2)
		begin
			hdrfill <= ECCBYTE(hdrfill, S_DATA);
			hdrsreg[14: 7] <= S_DATA;
			ivalid <= 0;
		end else if (icount == 3)
		begin
			hdrsreg <= { hdrsreg[29:7], hdrfill };
		end else
			hdrsreg <= { hdrsreg[29:0], 1'b0 };

		if (icount < 3)
			ivalid <= 0;
		else
			ivalid <= 1;

		idata <= { hdrsreg[30], S_DATA };

		if (icount < 3)
		begin
			b0fill <= 0;
			b1fill <= 0;
			b2fill <= 0;
			b3fill <= 0;
		end else begin
			b0fill <= ECCFN(ECCFN(b0fill, S_DATA[0]), S_DATA[4]);
			b1fill <= ECCFN(ECCFN(b1fill, S_DATA[1]), S_DATA[5]);
			b2fill <= ECCFN(ECCFN(b2fill, S_DATA[2]), S_DATA[6]);
			b3fill <= ECCFN(ECCFN(b3fill, S_DATA[3]), S_DATA[7]);
		end

	end else if (iready && icount >= IPKTLEN)
	begin
		ivalid <= !ilast;
		hdrsreg <= { hdrsreg[29:0], 1'b0 };
		idata  <= { hdrsreg[30],
				b3fill[6], b2fill[6], b1fill[6], b0fill[6],
				b3fill[7], b2fill[7], b1fill[7], b0fill[7] };

		b0fill <= { b0fill[5:0], 2'b00 };
		b1fill <= { b1fill[5:0], 2'b00 };
		b2fill <= { b2fill[5:0], 2'b00 };
		b3fill <= { b3fill[5:0], 2'b00 };
	end else if (iready)
		ivalid <= 0;
	// }}}

	// ilast
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		ilast <= 0;
	else if (ivalid && iready)
		ilast <= (icount == 3+OPKTLEN-1);// Set on icount==34=x22
	// }}}

	// loaded
	// {{{
	always @(posedge i_clk)
	if (i_reset || (!ivalid && fif_empty))
		loaded <= 0;
	else case({(ivalid && iready && ilast),(M_VALID && M_READY && M_LAST) })
	2'b10: loaded <= loaded + 1;
	2'b01: loaded <= loaded - 1;
	default: begin end
	endcase
	// }}}

	sfifo #(
		.BW(10), .LGFLEN(LGFLEN)
	) u_fifo(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wr(ivalid), .i_data({ ilast, idata }), .o_full(fif_full),
			.o_fill(fif_fill),
		.i_rd(loaded != 0 && M_READY),
			.o_data({ M_LAST, M_HDR, M_DATA }),
			.o_empty(fif_empty)
		// }}}
	);

	assign	M_VALID = !fif_empty && loaded != 0;
	assign	iready  = !fif_full;

	localparam	[7:0]	ECCPOLY= 8'hc1;

	function automatic [7:0] ECCFN(input [7:0] fill, input b);
		// {{{
	begin
		if (b ^ fill[7])
			ECCFN = { fill[6:0], 1'b0 } ^ ECCPOLY;
		else
			ECCFN = { fill[6:0], 1'b0 };
	end endfunction
	// }}}

	function automatic [7:0] ECCBYTE(input [7:0] fill, input [7:0] in);
		// {{{
		integer		ik;
		reg	[7:0]	lfill;
	begin
		lfill = fill;
		for(ik=0; ik<8; ik=ik+1)
			lfill = ECCFN(lfill, in[7-ik]);
		ECCBYTE = lfill;
	end endfunction
	// }}}

	always @(posedge i_clk)
	begin
		o_debug <= 32'h0;
		o_debug[31] <= M_VALID && M_READY && M_LAST;
		o_debug[30:24] <= M_DATA[6:0];
		o_debug[23] <= S_VALID;
		o_debug[22] <= S_READY;
		o_debug[21] <= S_LAST;
		//
		o_debug[20] <= M_VALID;
		o_debug[19] <= M_READY;
		o_debug[18] <= M_HDR;
		o_debug[17] <= M_LAST;
		//
		o_debug[16] <= ivalid;
		o_debug[15:10] <= icount;
		o_debug[  9] <= ilast;
		o_debug[8:3] <= fif_fill;
		o_debug[  2] <= (loaded != 0);
		o_debug[1:0] <= loaded[1:0];
	end

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, fif_fill };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
