`timescale	1ns/1ns
module	tb_arpcrc;

	reg	clk, reset;

	reg		s_valid, s_last, s_abort;
	reg	[63:0]	s_data;
	reg	[2:0]	s_bytes;
	wire		s_ready;

	wire		drop_valid, drop_last, drop_abort;
	wire	[63:0]	drop_data;
	wire	[2:0]	drop_bytes;
	wire		drop_ready;

	wire		m_valid, m_last, m_abort;
	wire	[63:0]	m_data;
	wire	[3:0]	m_bytes;
	wire		m_ready;

	////////////////////////////////////////////////////////////////////////
	//
	// CLK & RESET
	// {{{
	initial	clk = 0;
	always
		#5 clk = !clk;

	initial	begin
		reset <= 1;
		@(posedge clk);
		@(posedge clk);
		@(posedge clk)
			reset <= 1'b0;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// DUT: dropshort, crc_axin
	// {{{

	dropshort #(
		.DW(64)
	) u_dropshort (
		.S_CLK(clk), .S_ARESETN(!reset),

		.S_VALID(s_valid),
		.S_READY(s_ready),
		.S_DATA(s_data),
		.S_BYTES(s_bytes),
		.S_LAST(s_last),
		.S_ABORT(s_abort),

		.M_VALID(drop_valid),
		.M_READY(drop_ready),
		.M_DATA(drop_data),
		.M_BYTES(drop_bytes),
		.M_LAST(drop_last),
		.M_ABORT(drop_abort)
	);

	crc_axin
	u_crc (
		.ACLK(clk), .ARESETN(!reset),
		.i_cfg_en(1'b1),

		.S_AXIN_VALID(drop_valid),
		.S_AXIN_READY(drop_ready),
		.S_AXIN_DATA(drop_data),
		.S_AXIN_BYTES({ (drop_bytes == 0), drop_bytes }),
		.S_AXIN_LAST(drop_last),
		.S_AXIN_ABORT(drop_abort),

		.M_AXIN_VALID(m_valid),
		.M_AXIN_READY(m_ready),
		.M_AXIN_DATA(m_data),
		.M_AXIN_BYTES(m_bytes),
		.M_AXIN_LAST(m_last),
		.M_AXIN_ABORT(m_abort)
	);

	assign	m_ready = 1'b1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Test script: Send a packet
	// {{{
	initial begin
		s_valid = 1'b0;
		s_last  = 1'b0;
		s_abort = 1'b0;
		s_bytes = 3'b0;

		@(posedge clk);
		while(reset)
			@(posedge clk);
		@(posedge clk);

		@(posedge clk)
		begin
			s_valid <= 1'b1;
			s_data  <= { 8'h0a, 8'h00, 8'hff, 8'hff, 8'hff, 8'hff, 8'hff, 8'hff };
			s_bytes <= 3'h0;
			s_last  <= 1'b0;
		end

		@(posedge clk)
			s_data  <= { 8'h01, 8'h00, 8'h06, 8'h08, 8'h43, 8'h4f, 8'h44, 8'hcd };

		@(posedge clk)
			s_data  <= { 8'h0a, 8'h00, 8'h01, 8'h00, 8'h04, 8'h06, 8'h00, 8'h08 };

		@(posedge clk)
			s_data  <= { 8'hc9, 8'h03, 8'ha8, 8'hc0, 8'h43, 8'h4f, 8'h44, 8'hcd };

		@(posedge clk)
			s_data  <= { 8'ha8, 8'hc0, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00 };

		@(posedge clk)
			s_data  <= { 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'hc8, 8'h03 };

		@(posedge clk)
			s_data  <= { 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00 };

		@(posedge clk)
		begin
			s_data  <= { 8'h24, 8'hf6, 8'hd5, 8'h9c, 8'h00, 8'h00, 8'h00, 8'h00 };
			s_last <= 1'b1;
		end

		@(posedge clk)
		begin
			s_valid <= 1'b0;
			s_data  <= 64'h0;
			s_last  <= 1'b0;
		end

		while(m_valid)
			@(posedge clk);

		repeat (4)
			@(posedge clk);

		$finish;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// VCD
	// {{{
	initial	begin
		$dumpfile("arpcrc.vcd");
		$dumpvars(0, tb_arpcrc);
	end
	// }}}
endmodule
