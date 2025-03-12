////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/txfns.c
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
// Copyright (C) 2023-2025, Gisselquist Technology, LLC
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
//
// }}}
#include <stdint.h>
#include "board.h"
#include "txfns.h"

void	txchr(char ch);
void	txhex(unsigned val);
void	txstr(const char *str);

#define	ASM_TXCHR
#define	ASM_TXSTR
#define	ASM_TXHEX
#define	ASM_TXDECIMAL

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
#ifdef	ASM_TXCHR
asm("\t.global\ttxchr\n"
	// .file "txfns.c"
	// .text
	// .align\t2
	"\t.type\ttxchr, @function\n"
"txchr:\n"
	"\tLDI	_uart,R2\n"
".Ltxchr_loop:\n"
	"\tLW	4(R2),R3\n"
	"\tTEST	0x10000,R3\n"
	"\tBZ	.Ltxchr_loop\n"
	"\tSB	R1,15(R2)\n"
	"\tRETN\n"
	"\t.size\ttxchr, .-txchr\n");
#else
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
#endif

/*
 * txstr()
 *
 * Called to send a string to the UART port.  This works by calling txchr to
 * do its real work.
 */
#ifdef	ASM_TXSTR
asm(
	"\t.global\ttxstr\n"
	"\t.type\ttxstr, @function\n"
"txstr:\n"
	"\tTEST\tR1\n"
	"\tRETN.Z\n"
	"\tMOV\tR1,R2\n"
	"\tLB\t(R2),R1\n"
	"\tTEST\t255,R1\n"
	"\tRETN.Z\n"
	"\tSUB\t8,SP\n"
	"\tSW\tR0,(SP)\n"
	"\tSW\tR5,4(SP)\n"
	"\tMOV\tR2,R5\n"
	// R5 = *str
".Ltxstr_loop:\n"
	"\tJSR\ttxchr\n"
".Ltxstr_return:\n"
	"\tADD\t1,R5\n"
	"\tLB\t(R5),R1\n"
	"\tCMP\t0,R1\n"
	"\tMOV\t.Ltxstr_return(PC),R0\n"
	"\tBNZ\ttxchr\n"
	"\tLW\t(SP),R0\n"
	"\tLW\t4(SP),R5\n"
	"\tADD\t8,SP\n"
	"\tRETN\n"
	"\t.size\ttxstr, .-txstr\n");
#else
void    txstr(const char *str) {
	const	char *ptr = str;
	while(*ptr)
		txchr(*ptr++);
}
#endif

/*
 * txhex()
 *
 * Send a hexadecimal value to the output port
 */
#ifdef	ASM_TXHEX
asm(
"\t.global\ttxhex\n"
	"\t.type\ttxhex, @function\n"
"txhex:\n"
	"\tSUB\t12,SP\n"
	"\tSW\tR0,(SP)\n"
	"\tSW\tR5,4(SP)\n"
	"\tSW\tR6,8(SP)\n"
	"\t;\n"
	"\tMOV\tR1,R5\n"
	"\tLDI\t28,R6\n"
".Ltxhex_loop:\n"
	"\tMOV\tR5,R1\n"
	"\tLSR\tR6,R1\n"
	"\tAND\t15,R1\n"
	"\tCMP\t10,R1\n"
	"\tADD.GE\t7,R1\n"
	"\tADD\t0x30,R1\n"
	"\tJSR\ttxchr\n"
	"\tSUB\t4,R6\n"
	"\tBGE\t.Ltxhex_loop\n"
	"\t;\n"
	"\tLW\t(SP),R0\n"
	"\tLW\t4(SP),R5\n"
	"\tLW\t8(SP),R6\n"
	"\tADD\t12,SP\n"
	"\tRETN\n"
	"\t.size\ttxhex, .-txhex\n");
#else
void	txhex(unsigned val) {
	for(int i=28; i>=0; i-=4) {
		int ch = ((val>>i)&0x0f)+'0';
		if (ch > '9')
			ch = ch - '0'+'A'-10;
		txchr(ch);
	}
}
#endif

/*
 * txdecimal()
 *
 * Same as txhex, but for signed decimal numbers.
 */
#ifdef	ASM_TXDECIMAL
asm(
"\t.global\ttxdecimal\n"
	"\t.type\ttxdecimal, @function\n"
"txdecimal:\n"
	"\tCMP\t0,R1\n"
	"\tMOV.Z\t0x30,R1\n"
	"\tBZ\ttxchr\n"
	"\t; Sibling call--doesn't return\n"
	"\tSUB\t32,SP\n"
	"\tSW\tR0,20(SP)\n"
	"\tSW\tR5,24(SP)\n"
	"\tSW\tR6,28(SP)\n"
	"\t;\n"
	"\t; Deal with the sign bit\n"
	"\tMOV\tR1,R5	; R5 = UVAL\n"
	"\tMOV\t32,R1\n"
	"\tTEST\tR5\n"
	"\t; Optionally negate R5, if it was negative\n"
	"\tXOR.LT\t-1,R5\n"
	"\tADD.LT\t1,R5\n"
	"\t; Send either a space (already in R1) or a\n"
	"\t; minus sign\n"
	"\tMOV.LT\t0x2d,R1\n"
	"\tJSR\ttxchr\n"
	"\t;\n"
	"\tMOV\tSP,R6\n"
".Ltxdec_nextmodulo:\n"
	"\t; Calculate our digits\n"
	"\t;   There will always be at least one\n"
	"\tMOV\tR5,R1\n"
	"\tDIVU\t10,R5\t; R5 = UVAL / 10\n"
	"\tMOV\tR5,R3\n"
	"\tMPY\t10,R3\t; R3 = (UVAL / 10) * 10\n"
	"\tSUB\tR3,R1\t; = UVAL - (UVAL/10)*10\n"
	"\tADD\t0x30,R1\n"
	"\tSB\tR1,(R6)\n"
	"\tADD\t1,R6\n"
	"\tCMP\t0,R5\n"
	"\tBNZ\t.Ltxdec_nextmodulo\n"
	"\t; Transmit them, in reverse order\n"
".Ltxdec_nextout:\n"
	"\tSUB\t1,R6\n"
	"\tLB\t(R6),R1\n"
	"\tJSR\ttxchr\n"
	"\tCMP\tR6,SP\n"
	"\tBLT\t.Ltxdec_nextout\n"
	"\tLW\t20(SP),R0\n"
	"\tLW\t24(SP),R5\n"
	"\tLW\t28(SP),R6\n"
	"\tADD\t32,SP\n"
	"\tRETN\n"
	"\t.size\ttxdecimal, .-txdecimal\n");
#else
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
#endif
