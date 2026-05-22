////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/xqflex.v
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
// Copyright (C) 2024-2026, Gisselquist Technology, LLC
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
`timescale 1ns/1ps
`default_nettype	none
`ifdef	VERILATOR
`define	OPENSIM
`endif
`ifdef	IVERILOG
`define	OPENSIM
`endif
// }}}
module	xqflex #(
		// {{{
		parameter [0:0]		OPT_CLOCK = 1'b0,
		parameter [0:0]		OPT_PHASE = 1'b1
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		//
		input	wire		i_cs_n,
		input	wire	[1:0]	i_sck,
		input	wire	[3:0]	i_dat,
		output	wire	[3:0]	o_dat,
		input	wire	[1:0]	i_bmod,

		inout	wire		o_cs_n,
		inout	wire		o_sck,
		inout	wire	[3:0]	io_dat
		// }}}
	);

	genvar	gk;

	generate for(gk=0; gk<6; gk=gk+1)
	begin : IO

		wire	w_in, w_out;
		wire	high_z;

		if (gk >= 4)
		begin : UNIDIR_WIRE
			assign	high_z = 1'b0;
		end else begin : BIDIR_WIRES
			reg	r_z;

			// bmod enumeration
			// -----------------
			// 2'b00	NORMAL_SPI (pin[1] is high-z,o.w. drivn)
			// 2'b10	QUAD_WRITE	All data pins driven
			// 2'b11	QUAD_READ	All data pins in high-z
			initial	r_z = 1'b1;
			always @(posedge i_clk)
			if (!i_bmod[1])
				r_z <= (gk == 1);
			else
				r_z <= i_bmod[0];

			assign	high_z = r_z;
		end
`ifdef	OPENSIM
		// {{{
		// Verilator lint_off MULTIDRIVEN
		reg		r_pin;
		// Verilator lint_on  MULTIDRIVEN

		always @(posedge i_clk)
		if (gk < 4)
			r_pin <= i_dat[(gk < 4) ? gk : 0];
		else if (gk == 4)
			r_pin <= i_cs_n;
		else
			r_pin <= i_sck;

		assign	w_out = r_pin;

		if (gk <= 4)
		begin : DAT_PIN
			assign	io_dat[gk]  = (high_z) ? 1'bz : w_out;
		end else if (gk == 4)
		begin : CSN
			assign	o_cs_n = w_out;
		end else if (OPT_CLOCK)
		begin : GEN_SCK
			always @(negedge i_clk)
				r_pin <= 1'b0;

			assign	o_sck = w_out;
		end else begin : NO_SCK
			assign	o_sck = 1'b0;
		end
			
		// }}}
`else
		// Xilinx ODDR & IOBUF
		// {{{
		if (gk < 5 || OPT_CLOCK)
		begin : GEN_DATCSN
			wire	p, n;

			assign	p = (gk < 4) ? i_dat[gk]
					: (gk == 4) ? i_cs_n
					: (i_sck[1] && OPT_CLOCK);
			assign	n = (gk < 5) ? p : (i_sck[0] && OPT_CLOCK);

			ODDR #(
				// {{{
				.DDR_CLK_EDGE("SAME_EDGE"),
				.INIT(1'b1),
				.SRTYPE("SYNC")
				// }}}
			) u_oddr (
				// {{{
				.CE(1'b1), .R(1'b0), .S(1'b0),
				//
				.C(i_clk),
				.Q(w_out), .D1(p), .D2(n)
				// }}}
			);

			if (gk < 4)
			begin : IODAT
				IOBUF
				u_iobuf (
					.T(high_z), .O(w_in), .I(w_out),
					.IO(io_dat[gk])
				);
			end else if (gk == 4)
			begin : IOCSN
				OBUF u_obuf ( .I(w_out), .O(o_cs_n));
				assign	w_in  = 1'b0;
			end else // if (OPT_CLOCK)
			begin : IOCLK
				OBUF u_obuf ( .I(w_out), .O(o_sck));
				assign	w_in  = 1'b0;
			end
		end else if (gk == 5 && !OPT_CLOCK)
		begin : NOCLK
			reg	r_sck;

			always @(posedge i_clk)
				r_sck <= i_sck;

			assign	o_sck = r_sck;
		end
		// }}}
`endif

		if (gk < 4)
		begin : GEN_IDDR
`ifdef	OPENSIM
			// {{{
			reg	r_p, r_n, r_in;

			always @(posedge i_clk)
				r_p <= w_in;
			always @(negedge i_clk)
				r_n <= w_in;
			always @(posedge i_clk)
				r_in <= OPT_PHASE ? r_n : r_p;

			assign	io_dat[gk] = r_in;
			// }}}
`else
			// Xilinx IDDR
			// {{{
			wire	[1:0]	wide;

			IDDR #(
				.DDR_CLK_EDGE("SAME_EDGE_PIPELINED"),
				.INIT_Q1(1'b1),
				.INIT_Q2(1'b1),
				.SRTYPE("SYNC")
			) u_iddr (
				.C(i_clk), .CE(1'b1), .D(w_in),
				.R(1'b0), .S(1'b0),
				.Q1(wide[1]), .Q2(wide[0])
			);

			assign	o_dat[gk] = OPT_PHASE ? wide[0] : wide[1];
			// }}}
`endif
		end
	end endgenerate
endmodule
