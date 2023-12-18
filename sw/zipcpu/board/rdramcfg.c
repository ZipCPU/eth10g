////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rdramcfg.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Reads the DDR3 configuration data from the I2C pins on the DDR3
//		board.
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

#include <stdlib.h>
#include <stdio.h>
#include "zipcpu.h"
#include "zipsys.h"
#include "board.h"

#include "ddr3.c"

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
		"|  DDR3 I2C Configuration Reader / tester |\n"
		"+-----------------------------------------+\n");

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = WBSCOPE_DISABLE;

	// Now wait for the scope to prime
	while(0 == (_i2cscope->s_ctrl & WBSCOPE_PRIMED))
		;
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif

	// Make sure the I2C controller is halted from whatever else
	// it might've been doing.
	// {{{
	_i2c->ic_control = I2CC_CLEAR | I2CC_HARDHALT;
	do {
		c = _i2c->ic_control;
	} while(0 == (c & I2CC_STOPPED));

	printf("I2C Control = %08x\n", c);
	// }}}

	// Configure the I2C DMA to collect the data we need
	// {{{
	printf("Configuring the I2C DMA\n");

	// We'll put the configuration memory we read into an area of memory
	// pointed to by cfgmem
	cfgmem = (char *)malloc(512);
	_i2cdma->id_base   = (unsigned)cfgmem;
	_i2cdma->id_memlen = 512;

	// The DMA starts automatically when given a valid memory region.
	//   Now, whenever the I2C controller reads a byte of data, it will
	//   get automatically written to our memory region.
	// }}}

	// Request the data from the I2C controller
	// {{{
	printf("Commanding read DDR3 configuration sequence ...\n");

	_i2c->ic_address = (unsigned)i2casm;
#ifdef	_BOARD_HAS_I2CSCOPE
	_zip->z_tma = 0x00100000;
	while(_zip->z_tma != 0);
	_i2cscope->s_ctrl = WBSCOPE_TRIGGER;
#endif
	// }}}

	// Wait for the controller to complete
	// {{{
	do {
		c = _i2c->ic_control;
	} while(0 == (c & (I2CC_FAULT|I2CC_STOPPED))); // While not halted and not aborted

	if (0 == (c & I2CC_FAULT)) {
		// We aborted.  Now halt.  Hard halt.
		_i2c->ic_control = I2CC_HARDHALT;
	}
	// }}}

	if ((0 == (c & I2CC_FAULT)) && (c & I2CC_STOPPED)) {
		// We successfully read everything.  Examine the results
		// {{{
		CLEAR_DCACHE;
		printf("DDR3 Info:\n"
			"-------------------\n");

		ln = _i2cdma->id_current - _i2cdma->id_base;
		for(int k=0; k<ln; k++) {
			char	ch = cfgmem[k];

			printf("%02x%s", ch & 0x0ff,((k&15)==15) ? "\n" :", ");
		} printf("%02x\n", cfgmem[255] & 0x0ff);
		// }}}
	}
	else
		printf("I2C opn aborted.  Is the memory plugged in?\n");
#endif	// _BOARD_HAS_I2CDMA
#endif	// _BOARD_HAS_I2CCPU
}
