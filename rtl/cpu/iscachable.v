////////////////////////////////////////////////////////////////////////////////
//
// Filename:	iscachable.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A helper function to both dcache and its formal properties,
//		used to determine when a particular address is cachable.  This
//	module must be built of entirely combinatorial logic and nothing more.
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
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module	iscachable #(
		// {{{
		parameter	ADDRESS_WIDTH=32,
		localparam	AW = ADDRESS_WIDTH, // Just for ease of notation below
		parameter [AW-1:0] 	SDRAM_ADDR  = 0, SDRAM_MASK = 0,
		parameter [AW-1:0] 	BKRAM_ADDR = 32'h10000000,
					BKRAM_MASK = 32'h10000000,
		parameter [AW-1:0] 	FLASH_ADDR  = 0, FLASH_MASK  = 0
		// }}}
	) (
		// {{{
		input	wire	[AW-1:0]	i_addr,
		output	reg			o_cachable
		// }}}
	);


	always @(*)
	begin
		o_cachable = 1'b0;
		if ((SDRAM_ADDR !=0)&&((i_addr & SDRAM_MASK)== SDRAM_ADDR))
			o_cachable = 1'b1;
		else if ((FLASH_ADDR !=0)&&((i_addr & FLASH_MASK)== FLASH_ADDR))
			o_cachable = 1'b1;
		else if ((BKRAM_ADDR !=0)&&((i_addr & BKRAM_MASK)== BKRAM_ADDR))
			o_cachable = 1'b1;
	end

endmodule
