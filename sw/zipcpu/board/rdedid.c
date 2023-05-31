////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rdedid.c
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

#include "edid.c"

int main(int argc, char **argv) {
#ifndef	_BOARD_HAS_I2CCPU
	printf("ERR: This software requires the I2C controller\n");
#else
	unsigned	c = 0;
	printf("\n\n"
		"+---------------------------+\n"
		"|  I2C EDID Reader / tester |\n"
		"+---------------------------+\n");

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = 0x0400ffffu;

	// Now wait for the scope to prime
	while(0 == (_i2cscope->s_ctrl & 0x10000000u))
		;
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif

	_i2c->ic_control = 0x0780000;
	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0080000));

	printf("Commanding read EDID sequence ...\n");

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

	if (c & 0x080000) {
		printf("EDID Info:\n"
			"-------------------\n");

		for(int k=0; k<255; k++) {
			char	ch = _edid[k];

			printf("%02x%s", ch & 0x0ff,((k&15)==15) ? "\n" :", ");
		} printf("%02x\n", _edid[255] & 0x0ff);
	} else
		printf(".. I2C operation aborted.  Is the monitor plugged in?\n");
#endif
}
