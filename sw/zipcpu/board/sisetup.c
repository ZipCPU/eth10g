////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sisetup.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Sets up the Si5324 to produce a 148.5MHz output
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

#include <stdio.h>
#include "zipcpu.h"
#include "zipsys.h"
#include "board.h"

#include "si.c"

const unsigned	HOLDOFF = 0x0ffff;
int main(int argc, char **argv) {
#ifndef	_BOARD_HAS_I2CCPU
	printf("ERR: This software requires the I2C controller\n");
#else
	volatile char		readmem[16];
	volatile unsigned	c = 0;
	unsigned	alrm;
	printf("\n\n"
		"+-----------------------------+\n"
		"|  Si5324 Test setup via I2C  |\n"
		"+-----------------------------+\n");

	(*_sirefclk) = 0x20000000;	// 100MHz, system clock frequency
	(*_gpio) = GPIO_SET(GPIO_SIRESET);

	// Clear the I2C scope, and let it prime
	// {{{
#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = WBSCOPE_DISABLE | HOLDOFF;

	// Now wait for the scope to prime
	while(0 == (_i2cscope->s_ctrl & WBSCOPE_PRIMED))
		;
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif
	// }}}

	// Make sure the I2C controller is clear
	// {{{
	printf("Initial I2C control register: 0x%08x\n", _i2c->ic_control);
	_i2c->ic_control = I2CC_CLEAR;
	do {
		c = _i2c->ic_control;
	} while(0 == (c & I2CC_STOPPED));
	printf("        Control register: 0x%08x\n", _i2c->ic_control);
	printf("Initial clock counter   : 0x%08x\n", _i2c->ic_clkcount);
	// }}}

	printf("Commanding Si5324 sequence ...\n");

	_i2c->ic_address = (unsigned)siconfig;	// Start the transmission

	do {
		c = _i2c->ic_control;
	} while(0 == (c & I2CC_STOPPED)); // While not halted and not aborted

	if (0 == (c & I2CC_ABORT)) {
		// We aborted.  Now halt.  Hard halt.
		_i2c->ic_control = I2CC_CLEAR;
	}

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = WBSCOPE_TRIGGER | HOLDOFF;
#endif

	printf("I2C Control = %08x\n", c);
#ifdef	_BOARD_HAS_I2CSCOPE
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif

	if (c & I2CC_FAULT) {
		printf(".. Aborted\n");
		zip_halt();
	}

	printf("Si5324 setup complete\n");

	// Set up the I2C DMA
	// {{{
	_i2cdma->id_memlen = 0;
	_i2cdma->id_base = (unsigned)&readmem[0];
	_i2cdma->id_memlen = sizeof(readmem);
	// }}}

	for(int k=0; k<10; k++) {
		unsigned	nr;

		// Wait a second ..
		// {{{
		_zip->z_tma = 100000000;	// One second
		while(_zip->z_tma != 0)
			;
		// }}}

		// Now let's read back the interrupt/warning signs
		// {{{

		// Restart the scope
		// {{{
#ifdef	_BOARD_HAS_I2CSCOPE
		_i2cscope->s_ctrl = WBSCOPE_DISABLE | HOLDOFF;
		while(0 == (_i2cscope->s_ctrl & WBSCOPE_PRIMED))
			;
#endif
		// }}}

		// Command a DMA read
		_i2c->ic_address = (unsigned)sird;

		do {
			c = _i2c->ic_control;
		} while(0 == (c & I2CC_STOPPED)); // While not halted and not aborted

		if (c & I2CC_FAULT) {
			// We aborted.  Now halt.  Hard halt.
			_i2c->ic_control = I2CC_HARDHALT;
			printf("I2C ABORT!!\n");
			zip_halt();
		}

		CLEAR_DCACHE;

		nr = _i2cdma->id_current - _i2cdma->id_base;
		// printf("BASE:    %08x\n", _i2cdma->id_base);
		// printf("CURRENT: %08x\n", _i2cdma->id_current);
		// printf("NR:      %d\n", nr);
		if (nr == 0) {
#ifdef	_BOARD_HAS_I2CSCOPE
			_i2cscope->s_ctrl = WBSCOPE_TRIGGER | HOLDOFF;
			printf("Nothing read ... ??\n");
#endif
			zip_halt();
		}

// How are we setting ICMOS?
// Are we set for LVCMOS, or LVPECL outputs?
// Output frequency requires N1 >= 6 ?  What is N1?

printf("---\n");
		alrm = 0;
		for(int j=0; j<nr && j < sizeof(readmem); j++) {
			unsigned	ch = readmem[j] & 0x0ff;

			printf("  [%2d]: %02x\t", j, ch);
			switch(j) {
			case 0: printf("  x129, ALRM -- %3s %3s %3s\n",
				(ch & 4) ? "LOS2":"    ",
				(ch & 2) ? "LOS1":"    ",
				(ch & 1) ? "LOSX":"    ");
				alrm = alrm || (ch & 3);
				break;
			case 1: printf("  x130, ALRM -- %3s\n",
				(ch & 1) ? "LOL":"   ");
				alrm = alrm || (ch & 1);
				break;
			case 2: printf("  x131, FLAG -- %3s %3s %3s\n",
				(ch & 4) ? "LOS2":"    ",
				(ch & 2) ? "LOS ":"    ",
				(ch & 1) ? "LOSX":"    ");
				alrm = alrm || (ch & 3);
				break;
			case 3: printf("  x132, FLAG -- %3s\n",
				(ch & 2) ? "LOL_FLG":"   "); break;
			case 4: printf("  x134: PARTNUM[11:4]=%02x\n",ch);
				break;
			case 5: printf("  x135: PARTNUM[ 3:0]=%1x, DEVID=%1x\n",
				(ch >> 4)&0x0f, ch & 0x0f);
				break;
			case 6: printf("  x135, CAL  -- %3s %3s\n",
				(ch & 0x80) ? "RST":"   ",
				(ch & 0x40) ? "ICAL":"   "); break;
			default:
				printf("\n");
				break;
			}
		} if (alrm)
			k = 0;
		// }}}
	}

	// Now report on the clock speed ...
	// {{{
#ifdef	_BOARD_HAS_SICLKCOUNTER
	while(1) {
		// Wait a second ..
		// {{{
		_zip->z_tma = 100000000;	// One second
		while(_zip->z_tma != 0)
			;
		// }}}

#ifdef	_BOARD_HAS_REFCLKCOUNTER
		// Read and report the clock speed
		printf("REFCK: %08x\tSICLK: %08x\n",
			(*_sirefclkcounter), (*_siclk));
#else
		// Read and report the clock speed
		printf("SICLK: %08x\n",
			(*_siclk));
#endif
	}
#else
	printf("Ending early--no clk counters present\n");
#endif
	// }}}
#endif
}
