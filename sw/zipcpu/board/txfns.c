////////////////////////////////////////////////////////////////////////////////
//
// Filename:	txfns.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	These are some *very* simple UART routines, designed to support
//		a program before the C-library is up and running.  Once the
//	C-library is running on a device, it is anticipated that these routines
//	will no longer be needed or used--since they access the raw hardware
//	device(s).
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
//
// }}}
#include <stdint.h>
#include "board.h"
#include "txfns.h"

void	txchr(char ch);
void	txhex(unsigned val);
void	txstr(const char *str);

/*
 * txchr()
 *
 * This is the fundamental routine within here.  It transmits one character
 * out of the UART, polling the UART device to determine when/if it is idle
 * to send the next character.
 *
 */
// #define	UARTTX_READY	(_uart->u_fifo & 0x010000)
#define	UARTTX_READY	((_uart->u_tx & 0x0100) == 0)
// #define	UARTTX_READY	1
void	txchr(char val) {
	unsigned v = (unsigned char)val;
	static	int last_was_cr = 0;
	uint8_t	c;

	if ((0 == last_was_cr)&&(val == '\n')) {
		while(!UARTTX_READY)
			;
		c = '\r';
		_uart->u_tx = (unsigned)c;
	}

	while(!UARTTX_READY)
		;
	c = v;
	_uart->u_tx = (unsigned)c;
	last_was_cr = (c == '\r')?1:0;
}

/*
 * txstr()
 *
 * Called to send a string to the UART port.  This works by calling txchr to
 * do its real work.
 */
void    txstr(const char *str) {
	const	char *ptr = str;
	while(*ptr)
		txchr(*ptr++);
}

/*
 * txhex()
 *
 * Send a hexadecimal value to the output port
 */
void	txhex(unsigned val) {
	for(int i=28; i>=0; i-=4) {
		int ch = ((val>>i)&0x0f)+'0';
		if (ch > '9')
			ch = ch - '0'+'A'-10;
		txchr(ch);
	}
}

/*
 * txdecimal()
 *
 * Same as txhex, but for signed decimal numbers.
 */
void	txdecimal(int val) {
	char	tmp[16];
	int	nc=0, uval;

	if (val < 0) {
		uval = -val;
		txchr('-');
	} else {
		uval = val;
		txchr(' ');
	}

	if (uval == 0) {
		tmp[nc++] = '0';
	} else while(uval > 0) {
		unsigned dval, digit;
		dval = uval / 10;
		digit = (uval - dval * 10);
		tmp[nc++] = (digit + '0');
		uval = dval;
	}

	for(unsigned i=nc; i>0; i--)
		txchr(tmp[i-1]);
}
