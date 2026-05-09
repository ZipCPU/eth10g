module	IOBUF #(
		// Verilator lint_off UNUSED
		parameter	IBUF_LOW_PWR = 0,
		parameter	SLEW = 0
		// Verilator lint_on  UNUSED
	) (
		input	wire	I,
		input	wire	T,
		output	wire	O,
		inout	wire	IO
	);

	assign	IO = T ? 1'bz : I;
	assign	O  = IO;
endmodule
