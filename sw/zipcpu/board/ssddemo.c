////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	ssddemo.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Place a logo on the OLED/SSD1306 device.
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
#include "board.h"

#include "ssdlogo.c"

int main(int argc, char **argv) {
#ifndef	_BOARD_HAS_I2CCPU
	printf("ERR: This software requires the I2C controller\n");
#else
	unsigned	c = 0;
	printf("\n\n"
		"+--------------------+\n"
		"|  SSD Test via I2C  |\n"
		"+--------------------+\n");

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = 0x0400ffffu;

	// Now wait for the scope to prime
	while(0 == (_i2cscope->s_ctrl & 0x10000000u))
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
	printf("Commanding SSD sequence ...\n");

	_i2c->ic_address = (unsigned)i2casm;

	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0780000)); // While not halted and not aborted

	if (0 == (c & 0x080000)) {
		// We aborted.  Now halt.  Hard halt.
		_i2c->ic_control = 0x0080000;
	}

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = 0x8c00ffffu;
#endif

	printf("I2C Control = %08x\n", c);
#ifdef	_BOARD_HAS_I2CSCOPE
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif

	if (c & 0x080000) {
		printf("SSD setup complete\n");
	} else
		printf(".. Aborted\n");
#endif
}
