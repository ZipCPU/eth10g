module	IBUFDS (
		input	I, IB,
		output	O
	);

`ifdef	VERILATOR
	assign	O = I;
`else
	assign	O = ({ I, IB } === 2'b10) ? 1'b1
			: ({ I, IB } === 2'b01) ? 1'b0
			: 1'bx;
`endif
endmodule
