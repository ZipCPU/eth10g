////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	packet_generator.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Reads from a binary source file, and then uses that file to
//		generate a packet on the output port.
//
// Creator:	Sukru Uzun.
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
`timescale 1 ns/1 ps
`default_nettype none
// }}}
module packet_generator #(
		parameter PKTFILE = "ethernet_packet.bin"
	) (
		// {{{
		// clk, reset
		input	wire		S_AXI_ACLK,
		input	wire		S_AXI_ARESETN,
		//
		// Generated packet AXIN (AXI network packet) stream
		output	reg		M_VALID,
		input	wire		M_READY,
		output	reg	[31:0]	M_DATA,
		output	reg	[1:0]	M_BYTES,
		output	reg		M_LAST,
		output	reg		M_ABORT,
		//
		output	reg		M_FAULT,
		//
		output	reg		o_complete
		// }}}
	);

	// Local declarations
	// {{{
	reg [1:0] last_bytes;

	// Variables for file reading
	reg        end_of_packet;    // End-of-file flag
	reg        pkt_bit;          // pkt or idle
	reg        err_bit;          // fault option
	reg [29:0] idle_time;        // idle time for next packet
	reg [29:0] packet_length;    // packet length in terms of byte
	reg [31:0] crc;              // crc value
	reg [31:0] header;           // Size of the file
	reg [31:0] data;             // Data read from file
	reg [31:0] file_offset;      // Current offset in the file

	// File handle for file reading operation
	integer	file_handle;
	integer	scan_file;

	// The "USER_CLK" period is designed to be half of the time it takes
	// to send 64 bits--enough that delaying by a single user clock will
	// push us from on-cut to off cut.  This is the minimum resolution we
	// need in packet generation.
	localparam realtime USER_PERIOD = 33.0 * 1e9 / (10e9 * 66/64);
	reg	USER_CLK;
	// }}}

	initial begin
		USER_CLK = 1'b0;
		forever
			#(USER_PERIOD/2.0) USER_CLK = !USER_CLK;
	end

	assign M_BYTES = (M_LAST) ? (packet_length-(file_offset-4)):0;
	assign M_FAULT = err_bit;

	initial	if (PKTFILE == 0)
	begin
		M_VALID = 1'b0;
		// M_DATA,
		// M_BYTES,
		// M_LAST,
		M_ABORT = 1'b0;
		M_FAULT = 1'b0;
		o_complete = 1'b1;
	end else begin
        	// Give initial values to inputs
        	header = 0;
        	pkt_bit = 0;
        	err_bit = 0;
        	idle_time = 0;
        	data = 0;
        	M_VALID = 1'b0;
        	M_DATA  = 32'h0000;
        	M_LAST  = 1'b0;
        	M_ABORT = 1'b0;
		o_complete = 1'b0;

		// wait until reset clears
		while (!S_AXI_ARESETN)
			@(posedge S_AXI_ACLK);

		// Wait for the GTX transceiver to lock--about 10us
		#20000;

		// File reading operation
		$display("INFO: File operation is begun");
		file_handle = $fopen(PKTFILE, "rb");
		if (file_handle == 0) begin
			$display("ERROR: File could not be opened");
			$finish;
		end

		@(posedge S_AXI_ACLK);

		// Get the first packet header
		scan_file = $fread(data, file_handle);

		// main loop
		while (!$feof(file_handle))
		begin
			// Start reading from the beginning of the file
			file_offset = 0;
			end_of_packet = 0;

			header = ENDIAN_SWAP(data);
			pkt_bit = header[31];
			err_bit = header[30];
			$display("---------------------------");
			$display("Header:    %08x", header);
			$display("Packet bit:    %4d", pkt_bit);
			$display("Error bit:     %4d", err_bit);

			// Check packet bit
			if (pkt_bit)
			begin
				packet_length = header[29:0];
				$display("Packet length: %4d", packet_length);
			end else begin
				idle_time = header[29:0];
				$display("Idle time:     %4d", idle_time);
				repeat (idle_time)
					@(posedge USER_CLK);  // wait
				@(posedge S_AXI_ACLK);	// Sync to next clock
			end

			// Read the file and print its content to the console
			if (pkt_bit)
			begin // Output a packet
				// {{{
				while (!end_of_packet)
				begin // How to check whether FIFO full or not
					@(posedge S_AXI_ACLK)
					if(!M_VALID||M_READY)
					begin
						if (!$feof(file_handle)
							&& !end_of_packet)
						begin
							scan_file = $fread(data,
								file_handle);
							$display("%d. word: %x",
								file_offset/4,
								ENDIAN_SWAP(data));
						end

						if (packet_length <= file_offset + 4)
							end_of_packet <= 1;

						M_VALID <= !end_of_packet;
						M_DATA  <= ENDIAN_SWAP(data);
						if (packet_length
							<= file_offset + 4)
						begin
							case (packet_length - (file_offset - 4))
							2'b00: M_DATA        <= ENDIAN_SWAP(data);
							2'b01: M_DATA[31:8]  <= 24'b0;
							2'b10: M_DATA[31:16] <= 16'b0;
							2'b11: M_DATA[31:24] <= 8'b0;
							endcase
						end
						if (packet_length <= file_offset + 4)
							M_LAST <= 1;

						// increase offset (byte)
						file_offset <= file_offset + 4;
					end

					wait(!S_AXI_ACLK);
				end

				do begin
					@(posedge S_AXI_ACLK)
					if (M_READY)
					begin
						M_VALID <= 1'b0;
						M_LAST  <= 0;
						M_DATA  <= 32'h0000;
					end

					wait(!S_AXI_ACLK);
				end while (M_VALID);
				// }}}
			end

			// Read the next packet header
			scan_file = $fread(data, file_handle);
		end

		// Complete the file reading operation
		// $display("%d-)Packets are trasferred", channel_id);
		$fclose(file_handle);
		@(posedge S_AXI_ACLK)
			o_complete <= 1'b1;
	end

	// verilog gets little endian so we need swap endianness
	function [31:0] ENDIAN_SWAP(input [31:0] in_data);
	begin
		ENDIAN_SWAP = { in_data[ 7: 0], in_data[15: 8],
				in_data[23:16], in_data[31:24] };
	end endfunction

endmodule
