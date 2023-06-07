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
	unsigned	c = 0;
	printf("\n\n"
		"+-----------------------------+\n"
		"|  Si5324 Test setup via I2C  |\n"
		"+-----------------------------+\n");

	(*_sirefclk) = 0x20000000;	// 100MHz, system clock frequency
	(*_gpio) = GPIO_SET(GPIO_SIRESET);

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = WBSCOPE_DISABLE | HOLDOFF;

	// Now wait for the scope to prime
	while(0 == (_i2cscope->s_ctrl & WBSCOPE_PRIMED))
		;
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif

	printf("Initial control register: 0x%08x\n", _i2c->ic_control);
	_i2c->ic_control = 0x0780000;
	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0080000));
	printf("        Control register: 0x%08x\n", _i2c->ic_control);

	printf("Initial clock counter   : 0x%08x\n", _i2c->ic_clkcount);
	printf("Commanding Si5324 sequence ...\n");

	_i2c->ic_address = (unsigned)siconfig;

	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0780000)); // While not halted and not aborted

	if (0 == (c & 0x080000)) {
		// We aborted.  Now halt.  Hard halt.
		_i2c->ic_control = 0x0080000;
	}

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = WBSCOPE_TRIGGER | HOLDOFF;
#endif

	printf("I2C Control = %08x\n", c);
#ifdef	_BOARD_HAS_I2CSCOPE
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif

	if (0 == (c & 0x080000)) {
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
#ifdef	_BOARD_HAS_I2CSCOPE
		_i2cscope->s_ctrl = WBSCOPE_DISABLE | HOLDOFF;
		while(0 == (_i2cscope->s_ctrl & WBSCOPE_PRIMED))
			;
#endif
		_i2c->ic_address = (unsigned)sird;

		do {
			c = _i2c->ic_control;
		} while(0 == (c & 0x0780000)); // While not halted and not aborted

		if (0 == (c & 0x080000)) {
			// We aborted.  Now halt.  Hard halt.
			_i2c->ic_control = 0x0080000;
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

		for(int k=0; k<nr && k < sizeof(readmem); k++) {
			unsigned	ch = readmem[k] & 0x0ff;

			printf("  [%2d]: %02x\t", k, ch);
			switch(k) {
			case 0: printf("  x129, ALRM -- %03s %03s %03s\n",
				(ch & 4) ? "LOS2":"    ",
				(ch & 2) ? "LOS1":"    ",
				(ch & 1) ? "LOSX":"    "); break;
			case 1: printf("  x130, ALRM -- %03s\n",
				(ch & 1) ? "LOL":"   "); break;
			case 2: printf("  x131, FLAG -- %03s %03s %03s\n",
				(ch & 4) ? "LOS2":"    ",
				(ch & 2) ? "LOS ":"    ",
				(ch & 1) ? "LOSX":"    "); break;
			case 3: printf("  x132, FLAG -- %03s\n",
				(ch & 1) ? "LOL":"   "); break;
			case 4: printf("  x134: PARTNUM[11:4]=%02x\n",ch);
				break;
			case 5: printf("  x135: PARTNUM[3:0]=%1x, DEVID=%1x\n",
				(ch >> 4)&0x0f, ch & 0x0f);
				break;
			default:
				printf("\n");
				break;
			}
		}
		// }}}
	}

#endif
}
