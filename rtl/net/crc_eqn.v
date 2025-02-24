////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/crc_eqn.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	It can be a challenge to run a CRC at high speed.  This helper
//		module attempts to make that easier, by noting that all CRC
//	bits are generated from a simple linear equation.  Hence, if you just
//	know that equation, you can calculate each CRC bit, as in ...
//
//	crc_bit[k] = ^(EQUATION[k] & inputs)
//
//	This is a direct computation method, and should result in simplified
//	logic usage.  We just need to calculate the EQUATION (below) for this
//	purpose.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2025, Gisselquist Technology, LLC
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
module	crc_eqn #(
		// {{{
		parameter	DW = 64,
				CRC_BITS = 32,
		parameter [CRC_BITS-1:0] POLYNOMIAL = 32'hedb88320
		// }}}
	) (
		// {{{
		input	wire	[DW-1:0]	skd_data,
		input	wire	[CRC_BITS-1:0]	crc32,
		output	reg	[CRC_BITS*(DW/8)-1:0]	next_crc_wide
		// }}}
	);

	localparam [(CRC_BITS*(DW/8))*(DW+CRC_BITS)-1:0] EQUATION
				= GEN_EQUATION(1'b0);

	integer	ik;

	// Verilator lint_off UNUSED
	function [(CRC_BITS*(DW/8))*(DW+CRC_BITS)-1:0] GEN_EQUATION(input ign);
	// {{{
		reg	[DW-1:0]	dfill;
		reg	[CRC_BITS-1:0]	cfill;
		integer			octet_steps, r, eqn, ii;

		reg	[DW+CRC_BITS-1:0]	mxbit;
	begin
		GEN_EQUATION = 0;
		// For (DW+CRC_BITS) bits in,
		//		Where the first DW bits are data bits, and the
		//		last CRC_BITS are the prior CRC bits from the
		//		last run
		//	Produce CRC * (DW/8) bits out
		//	The first CRC bits out will be associated with running
		//	  the CRC (and data) for DW/8 bits.
		//	The second set of CRC bits out will be due to running
		//	  for 2*DW/8 clock cycles
		//	The third set of CRC bits out will be due to running
		//	  for 3*DW/8 clock cycles
		//	etc.
		//
		// GEN_EQUATION therefore represents a matrix that is
		//	(CRC_BITS * (DW/8)) x (DW + CRC_BITS)	in size.
		// It is represented in row form, so that
		//	GEN_EQUATION[y * (DW+CRC_BITS) +: (DW+CRC_BITS)]
		//		constitues the equation to generate one output
		//		bit, bit y.
		//	For (0 <= y < CRC_BITS), this will be the CRC associated
		//	with stepping by 8 of the DW bits only, and thus be
		//	associated with generating bits [CRC_BITS-1:0] of the
		//	CRC after these 8 steps.
		//
		//	For (CRC_BITS <= y < 2*CRC_BITS), this will yield the
		//	equations for the CRC associated with stepping 16 times.
		//	As before, this will be bits [CRC_bits-1:0] of that
		//	second CRC.
		//
		for(ii=0; ii<CRC_BITS+DW; ii=ii+1)
		begin // Walk through each potential input bit, first through
			// the potential CRC inputs, then through the potential
			// data inputs.  'ii' represents which input bit we are
			// starting from.  'ii' >= CRC_BITS will reference an
			// input data bit, whereas 'ii' < CRC_BITS will
			// reference an input from the previous CRC state.
			//

			// We'll step this input between 8 and 8*(DW/8) times
			for(octet_steps=1; octet_steps<=(DW/8);
						octet_steps=octet_steps+1)
			begin
				// Assume an input value of 1<<i
				//	This needs to be spread across all
				//	possible { data, crc } potential input
				//	bits.
				// We'd nominally write { dfill, cfill } = 1<<ii
				// save that Verilator doesn't like this in a
				// function.
				dfill = 0;
				cfill = 0;
				if (ii < CRC_BITS)
					cfill[ii] = 1;
				else
					dfill[ii - CRC_BITS] = 1;

				for(r=0; r<8*octet_steps; r=r+1)
				begin
					if (cfill[0] ^ dfill[0])
						cfill = (cfill >> 1)
								^ POLYNOMIAL;
					else
						cfill = (cfill >> 1);
					dfill = dfill >> 1;
				end

				// We now know the contribution from bit 'ii'.
				// Sadly, this contribution will take place
				// across *many* equations, so we now need to
				// walk through all of the equations this bit
				// might contribute to, one equation at a time,
				// setting the appropriate bit within them.
				//
				// Note we are setting a single bit  at a time
				// here.
				for(eqn=0; eqn<CRC_BITS; eqn=eqn+1)
				begin
					mxbit = { dfill, cfill } >> eqn;
					GEN_EQUATION[((octet_steps-1) * CRC_BITS + eqn)
						*(CRC_BITS+DW) + ii] = mxbit[0];
				end
			end
		end
	end endfunction
	// }}}
	// Verilator lint_on  UNUSED

	always @(*)
	for(ik=0; ik<CRC_BITS*(DW/8);ik=ik+1)
		next_crc_wide[ik] = ^({ skd_data, crc32 }
				& EQUATION[(CRC_BITS+DW)*ik +: (CRC_BITS+DW)]);

`ifdef	DEBUG
	// For debugging purposes, it can help to look at each of the equations,
	// one at a time, and verify them by hand.  This just separates one
	// equation from the matrix, and places it in the trace.
	(* keep *) wire	[CRC_BITS+DW-1:0]	eqnx;
	assign	eqnx = EQUATION[(CRC_BITS-9)*(CRC_BITS+DW) +: (CRC_BITS+DW)];
`endif
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal property checking
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	function [CRC_BITS-1:0]	CRC_STEP(input data,
					input [CRC_BITS-1:0] prior);
		// {{{
	begin
		if (data ^ prior[0])
			CRC_STEP = (prior >> 1) ^ POLYNOMIAL;
		else
			CRC_STEP = (prior >> 1);
	end endfunction
	// }}}

	function [CRC_BITS-1:0]	BYTE_STEP(input [7:0] data,
					input [CRC_BITS-1:0] prior);
		// {{{
		integer			step;
		reg [CRC_BITS-1:0]	state;
	begin
		state = CRC_STEP(data[0], prior);
		for(step=1; step<8; step=step+1)
			state = CRC_STEP(data[step], state);
		BYTE_STEP = state;
	end endfunction
	// }}}

	function [CRC_BITS-1:0]	WORD_STEP(input [DW-1:0] data,
					input [CRC_BITS-1:0] prior);
		// {{{
		integer			step;
		reg [CRC_BITS-1:0]	state;
	begin
		state = CRC_STEP(data[0], prior);
		for(step=1; step<DW; step=step+1)
			state = CRC_STEP(data[step], state);
		WORD_STEP = state;
	end endfunction
	// }}}

	always @(*)
	begin
		// Just to make the proof go faster, let's limit the number
		// of potential inputs.  DO NOT AGGREGATE THIS FILE UP A
		// LEVEL WITH THESE ASSUMPTIONS IN PLACE!!
		assume($onehot(skd_data));
		assume($onehot(crc32));

		// Since this is all linear (by visual desk check of the
		// next_crc_wide assignment line), then if that limited set of
		// inputs works, then all inputs should work.

		assert(next_crc_wide[CRC_BITS-1:0]
					== BYTE_STEP(skd_data[7:0], crc32));

		assert(next_crc_wide[CRC_BITS*((DW/8)-1) +: CRC_BITS]
			== WORD_STEP(skd_data, crc32));
	end
`endif
// }}}
endmodule
