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
