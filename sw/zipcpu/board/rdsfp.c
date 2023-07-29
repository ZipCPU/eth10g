////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rdsfp.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Reads the SFP+ I2C data from all four of the I2C devices in the
//		system.  (Based on the instructions given in sfp.c ...)
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
// }}}

#include <stdlib.h>
#include <stdio.h>
#include "zipcpu.h"
#include "zipsys.h"
#include "board.h"

#include "sfp.c"

int main(int argc, char **argv) {
#ifndef	_BOARD_HAS_I2CCPU
	printf("ERR: This software requires the I2C controller\n");
#else
#ifndef	_BOARD_HAS_I2CDMA
	printf("ERR: This software requires the I2C DMA\n");
#else

	char	*cfgmem;
	unsigned	c = 0, ln = 0;
	printf("\n\n"
		"+-----------------------------------------+\n"
		"|  SFP+ I2C Configuration Reader / tester |\n"
		"+-----------------------------------------+\n");

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = 0x04000000u;

	// Now wait for the scope to prime
	while(0 == (_i2cscope->s_ctrl & 0x10000000u))
		;
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif

	// Make sure the I2C controller is halted from whatever else
	// it might've been doing.
	// {{{
	_i2c->ic_control = 0x0780000;
	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0080000));

	printf("I2C Control = %08x\n", c);
	// }}}

	// Configure the I2C DMA to collect the data we need
	// {{{
	printf("Configuring the I2C DMA\n");

	// We'll put the configuration memory we read into an area of memory
	// pointed to by cfgmem
	cfgmem = (char *)malloc(1024);
	_i2cdma->id_base   = (unsigned)cfgmem;
	_i2cdma->id_memlen = 1024;

	// The DMA starts automatically when given a valid memory region.
	//   Now, whenever the I2C controller reads a byte of data, it will
	//   get automatically written to our memory region.
	// }}}

	// Request the data from the I2C controller
	// {{{
	printf("Commanding read SFP+ data areas ...\n");

	_i2c->ic_address = (unsigned)i2casm;
#ifdef	_BOARD_HAS_I2CSCOPE
	_zip->z_tma = 0x00100000;
	while(_zip->z_tma != 0);
	_i2cscope->s_ctrl = 0x8c000000u;
#endif
	// }}}

	// Wait for the controller to complete
	// {{{
	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0780000)); // While not halted and not aborted

	if (0 == (c & 0x080000)) {
		// We aborted.  Now halt.  Hard halt.
		_i2c->ic_control = 0x0080000;
	}
	// }}}

	if (c & 0x080000) {
		// We successfully read everything.  Examine the results
		// {{{
		CLEAR_DCACHE;
		printf("SFP+ Info:\n"
			"-------------------\n");

		ln = _i2cdma->id_current - _i2cdma->id_base;
		for(int k=0; k+95<ln; k+=96) {
			printf("Device #%d\n", k/96);
			for(int j=k; j<k+95; j++) {
				char	ch = cfgmem[j];

				printf("%02x%s", ch & 0x0ff,((j&15)==15) ? "\n" :", ");
			} printf("%02x\n", cfgmem[k+95] & 0x0ff);
		}
		// }}}
	}
	else
		printf("I2C opn aborted.  Is the memory plugged in?\n");
#endif	// _BOARD_HAS_I2CDMA
#endif	// _BOARD_HAS_I2CCPU
}

/*
+-----------------------------------------+
|  SFP+ I2C Configuration Reader / tester |
+-----------------------------------------+
I2C Scope   = 16a00000
I2C Control = 0008f0a3
Configuring the I2C DMA
Commanding read SFP+ data areas ...
SFP+ Info:
-------------------
Device #0
50, 00, f6, 00, 4b, 00, fb, 00, 90, 88, 71, 48, 88, b8, 79, 18
1f, 40, 03, e8, 1d, 4c, 05, dc, 27, 10, 03, 1a, 22, d0, 03, 7b
31, 2d, 00, 3f, 27, 10, 00, 46, 00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 3f, 80, 00, 00, 00, 00, 00, 00, 01, 00, 00, 00
01, 00, 00, 00, 01, 00, 00, 00, 01, 00, 00, 00, 00, 00, 00, 63
Device #1
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
Device #2
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
Device #3
50, 00, f6, 00, 4b, 00, fb, 00, 90, 88, 71, 48, 88, b8, 79, 18
1f, 40, 03, e8, 1d, 4c, 05, dc, 27, 10, 03, 1a, 22, d0, 03, 7b
31, 2d, 00, 3f, 27, 10, 00, 46, 00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 3f, 80, 00, 00, 00, 00, 00, 00, 01, 00, 00, 00
01, 00, 00, 00, 01, 00, 00, 00, 01, 00, 00, 00, 00, 00, 00, 63
*/
