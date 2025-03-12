////////////////////////////////////////////////////////////////////////////////
//
// Filename:	pktstats.txt
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
// Copyright (C) 2025, Gisselquist Technology, LLC
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
`default_nettype none
// }}}
module	pktstats #(
		parameter	WIDTH = 48
	) (
		// {{{
		input	wire		i_clk,
					i_reset,
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[4:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		//
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		//
		input	wire		i_valid,
		input	wire	[30:0]	i_data
		// }}}
	);

	// Local declarations
	// {{{
	reg		lcl_reset;

	reg		rx_last, crc_last, tx_last, gate_last;
	reg		rx_overflow, crc_overflow, tx_overflow, gate_overflow;

	reg [WIDTH-1:0]	rx_abort_count, crc_abort_count, tx_abort_count,
			gate_abort_count;

	reg [WIDTH-1:0]	rx_byte_count, crc_byte_count, tx_byte_count,
			gate_byte_count;

	reg [WIDTH-1:0]	rx_pkt_count, crc_pkt_count, tx_pkt_count,
			gate_pkt_count;
	// }}}

	always @(posedge i_clk)
		lcl_reset <= i_reset || (i_wb_stb && i_wb_we && i_wb_sel != 0);

	// Last update
	// {{{
	always @(posedge i_clk)
	if (i_reset || lcl_reset)
	begin
		// {{{
		rx_last   <= 0;
		crc_last  <= 0;
		tx_last   <= 0;
		gate_last <= 0;
		// }}}
	end else begin
		rx_last  <= 0;
		crc_last <= 0;
		tx_last  <= 0;
		gate_last<= 0;

		if (i_valid) // There is no i_ready
		begin
			case(i_data[26+: 3])
			3'b100: rx_last   <= (&rx_pkt_count[31:0])
					||(&rx_byte_count[31:20])
					||(&rx_abort_count[31:0]);

			3'b101: crc_last  <= (&crc_pkt_count[31:0])
					||(&crc_byte_count[31:20])
					||(&crc_abort_count[31:0]);

			3'b110: tx_last   <= (&tx_pkt_count[31:0])
					||(&tx_byte_count[31:20])
					||(&tx_abort_count[31:0]);

			3'b111: gate_last <= (&gate_pkt_count[31:0])
					||(&gate_byte_count[31:20])
					||(&gate_abort_count[31:0]);
			default: begin end
			endcase
		end
	end
	// }}}

	// Generate counters
	// {{{
	always @(posedge i_clk)
	if (i_reset || lcl_reset)
	begin
		// {{{
		rx_overflow    <= 0;
		rx_abort_count <= 0;
		rx_byte_count  <= 0;
		rx_pkt_count   <= 0;

		crc_overflow    <= 0;
		crc_abort_count <= 0;
		crc_byte_count  <= 0;
		crc_pkt_count   <= 0;

		tx_overflow    <= 0;
		tx_abort_count <= 0;
		tx_byte_count  <= 0;
		tx_pkt_count   <= 0;

		gate_overflow    <= 0;
		gate_abort_count <= 0;
		gate_byte_count  <= 0;
		gate_pkt_count   <= 0;
		// }}}
	end else if (i_valid) // There is no i_ready
	begin
		case(i_data[26+: 3])
		3'b100: if (!rx_overflow)
			// {{{
			begin
				if (i_data[19])
					{ rx_overflow, rx_abort_count } <= rx_abort_count + 1;
				else begin
					{ rx_overflow, rx_byte_count  } <= rx_byte_count + { {(WIDTH-17){1'b0}}, i_data[18:2] };
					rx_pkt_count <= rx_pkt_count + 1;
				end
			end
			// }}}
		3'b101: if (!crc_overflow)
			// {{{
			begin
				if (i_data[19])
					{ crc_overflow, crc_abort_count } <= crc_abort_count + 1;
				else begin
					{ crc_overflow, crc_byte_count  } <= crc_byte_count + { {(WIDTH-17){1'b0}}, i_data[18:2] };
					crc_pkt_count <= crc_pkt_count + 1;
				end
			end
			// }}}
		3'b110: if (!tx_overflow)
			// {{{
			begin
				if (i_data[19])
					{ tx_overflow, tx_abort_count } <= tx_abort_count + 1;
				else begin
					{ tx_overflow, tx_byte_count  } <= tx_byte_count + { {(WIDTH-17){1'b0}}, i_data[18:2] };
					tx_pkt_count <= tx_pkt_count + 1;
				end
			end
			// }}}
		3'b111: if (!gate_overflow)
			// {{{
			begin
				if (i_data[19])
					{ gate_overflow, gate_abort_count } <= gate_abort_count + 1;
				else begin
					{ gate_overflow, gate_byte_count  } <= gate_byte_count+ { {(WIDTH-17){1'b0}}, i_data[18:2] };
					gate_pkt_count <= gate_pkt_count + 1;
				end
			end
			// }}}
		default: begin end
		endcase
	end
	// }}}

	assign	o_wb_stall = 1'b0;

	// ACK
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= i_wb_stb && !o_wb_stall;
	// }}}

	// Read counters via the bus
	// {{{
	always @(posedge i_clk)
	begin
		o_wb_data <= 0;

		case(i_wb_addr)
		5'd0: if (rx_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= rx_pkt_count[31:0];
		5'd1: begin
			if (rx_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= rx_pkt_count[WIDTH-1:32];
			o_wb_data[31] <= rx_last;
			end

		5'd2: if (rx_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= rx_byte_count[31:0];
		5'd3: begin
			if (rx_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= rx_byte_count[WIDTH-1:32];
			o_wb_data[31] <= rx_last;
			end

		5'd4: if (rx_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= rx_abort_count[31:0];
		5'd5: begin
			if (rx_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= rx_abort_count[WIDTH-1:32];
			o_wb_data[31] <= rx_last;
			end

		5'd6: if (crc_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= crc_pkt_count[31:0];
		5'd7: begin
			if (crc_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= crc_pkt_count[WIDTH-1:32];
			o_wb_data[31] <= crc_last;
			end

		5'd8: if (crc_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= crc_byte_count[31:0];
		5'd9: begin
			if (crc_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= crc_byte_count[WIDTH-1:32];
			o_wb_data[31] <= crc_last;
			end

		5'd10: if (crc_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= crc_abort_count[31:0];
		5'd11: begin
			if (crc_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= crc_abort_count[WIDTH-1:32];
			o_wb_data[31] <= crc_last;
			end

		5'd12: if (tx_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= tx_pkt_count[31:0];
		5'd13: begin
			if (tx_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= tx_pkt_count[WIDTH-1:32];
			o_wb_data[31] <= tx_last;
			end

		5'd14: if (tx_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= tx_byte_count[31:0];
		5'd15: begin
			if (tx_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= tx_byte_count[WIDTH-1:32];
			o_wb_data[31] <= tx_last;
			end

		5'd16: if (tx_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= tx_abort_count[31:0];
		5'd17: begin
			if (tx_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= tx_abort_count[WIDTH-1:32];
			o_wb_data[31] <= tx_last;
			end

		5'd18: if (gate_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= gate_pkt_count[31:0];
		5'd19: begin
			if (gate_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= gate_pkt_count[WIDTH-1:32];
			o_wb_data[31] <= gate_last;
			end

		5'd20: if (gate_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= gate_byte_count[31:0];
		5'd21: begin
			if (gate_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= gate_byte_count[WIDTH-1:32];
			o_wb_data[31] <= gate_last;
			end

		5'd22: if (gate_overflow)
			o_wb_data <= 32'hffff_ffff;
			else
			o_wb_data[31:0] <= gate_abort_count[31:0];
		5'd23: begin
			if (gate_overflow)
				o_wb_data <= 32'hffff_ffff;
			else
				o_wb_data[0 +: (WIDTH-32)] <= gate_abort_count[WIDTH-1:32];
			o_wb_data[31] <= gate_last;
			end
		default: begin end
		endcase

		if (!i_wb_stb || i_wb_we || i_wb_sel == 0)
			o_wb_data <= 0;
	end
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_data, i_data[30:29], i_data[25:20], i_data[1:0] };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
