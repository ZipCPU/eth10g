////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/ssddemo.c
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
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
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
