////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/rdedid.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Reads the EDID (Extended Display Identification Data) from the
//		downstream (i.e. hdmitx) monitor.
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
#include "zipsys.h"
#include "board.h"

#include "edid.c"

#ifndef	_BOARD_HAS_I2CCPU
#define	NO_ACCESS
#else
#ifndef	EDID_ACCESS
#define	NO_ACCESS
#endif
#endif

int main(int argc, char **argv) {
#ifdef	NO_ACCESS
	printf("ERR: This software requires both the I2C and EDID controllers\n");
#else
	unsigned	c = 0;
	printf("\n\n"
		"+---------------------------+\n"
		"|  I2C EDID Reader / tester |\n"
		"+---------------------------+\n");

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = 0x04000000u;

	// Now wait for the scope to prime
	while(0 == (_i2cscope->s_ctrl & 0x10000000u))
		;
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif

	_i2c->ic_control = 0x0780000;
	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0080000));

	printf("I2C Control = %08x\n", c);
	printf("Commanding read EDID sequence ...\n");

	_i2c->ic_address = (unsigned)i2casm;
#ifdef	_BOARD_HAS_I2CSCOPE
	_zip->z_tma = 0x00100000;
	while(_zip->z_tma != 0);
	_i2cscope->s_ctrl = 0x8c000000u;
#endif

	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0780000)); // While not halted and not aborted

	if (0 == (c & 0x080000)) {
		// We aborted.  Now halt.  Hard halt.
		_i2c->ic_control = 0x0080000;
	}

// #ifdef	_BOARD_HAS_I2CSCOPE
//	_i2cscope->s_ctrl = 0x8c00ffffu;
// #endif

	if (c & 0x080000) {
		printf("EDID Info:\n"
			"-------------------\n");

		for(int k=0; k<255; k++) {
			char	ch = _edid[k];

			printf("%02x%s", ch & 0x0ff,((k&15)==15) ? "\n" :", ");
		} printf("%02x\n", _edid[255] & 0x0ff);
#ifdef	_BOARD_HAS_I2CSCOPE
	// _zip->z_tma = 0x0ffffff;
	// while(_zip->z_tma != 0);
	// _i2cscope->s_ctrl = 0x8c00ffffu;
	// printf("Scope complete\n");
#endif

	} else
		printf(".. I2C operation aborted.  Is the monitor plugged in?\n");
#endif
}
