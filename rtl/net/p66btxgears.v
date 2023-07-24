////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/p66btxgears.v
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
`default_nettype none
// }}}
module	p66btxgears // #()
	(
		input	wire	i_clk,
		input	wire	i_reset,
		//
		// input wire		S_VALID,
		output	reg		S_READY,
		input	wire	[65:0]	S_DATA,
		//
		output	wire	[63:0]	o_data
	);

	reg	[4:0]	r_count;
	reg	[129:0]	gearbox;

	always @(posedge i_clk)
	if (i_reset)
	begin
		r_count <= 0;
		S_READY <= 0;
	end else if (S_READY)
	begin
		r_count <= r_count + 1; // i.e., plus (66 - 64) /2;
		S_READY <= r_count < 31;
	end else begin
		r_count <= 0;
		S_READY <= 1;
	end

	always @(posedge i_clk)
	if (i_reset)
		gearbox <= 130'h0;
	else if (S_READY)
		gearbox <= { 64'h0, gearbox[129:64]}
				| ({ 64'h0, S_DATA } << { r_count, 1'b0 });
	else
		gearbox <= { 64'h0, gearbox[129:64]};

	assign	o_data = gearbox[63:0];

	/*
	function automatic [65:0] BITREV(input [65:0] in);
		integer ik;
	begin
		for(ik=0; ik<66; ik=ik+1)
			BITREV[ik] = in[65-ik];
	end endfunction	
	*/
endmodule
