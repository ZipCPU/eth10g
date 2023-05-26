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
#ifndef	_BOARD_HAS_I2C
	printf("ERR: This software requires the I2C controller\n");
#else
	printf("Initial control register: 0x%08x\n", _i2c->ic_control);
	printf("Initial clock counter   : 0x%08x\n", _i2c->ic_clkcount);
	printf("Commanding SSD sequence ...\n");
	_i2c->ic_address = (unsigned)i2casm;

	unsigned	c = 0;
	do {
		c = i2c->ic_control;
	} while(0 == (c & 0x080000)); // While not halted
	printf("SSD setup complete\n");
#endif
}
