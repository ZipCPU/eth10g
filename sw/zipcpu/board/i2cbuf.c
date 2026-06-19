////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/i2cbuf.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2025-2026, Gisselquist Technology, LLC
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
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include "txfns.h"
#include "i2cbuf.h"
// }}}

#define	I2CB_NOOP	0
#define	I2CB_START	1
#define	I2CB_STOP	2
#define	I2CB_SEND	3
#define	I2CB_READ	4
#define	I2CB_RNAK	5
	// RLSTACK	6
#define	I2CB_RLAST	7
#define	I2CB_WAIT	8
#define	I2CB_HALT	9
#define	I2CB_ABORT	10
#define	I2CB_TARGET	11
#define	I2CB_JUMP	12
#define	I2CB_CHANNEL	13

/*
typedef	struct	I2CBUF_S {
		// i_ln: The (current) number of bytes in use in our buffer.
		//  As such, the next byte will (always) go into i_b[i_ln++].
		//  If i_half is true, the next nibble will go into the least
		//  significant nibble of i_b[i_ln-1].
	int	i_ln,
		// i_bufsz: The number of bytes in our buffer.
		i_bufsz,
		// i_half: true if only the first nibble has been used, and
		//  so the second half-nibble is still available.  If i_half
		//  is true, then i_b[i_ln] points to a word that is half
		//  filled.  This must be so, otherwise any data copies
		//  would fail.
		i_half,
		// i_b: a pointer to the buffer we are using to keep track
		// of everything.
	char	i_b[1];
} I2CBUF;
*/

I2CBUF *i2cb_new(int sz) {
	// {{{
	I2CBUF	*ib;

	sz += 3;
	sz &= ~0x03;
	ib = malloc(sizeof(I2CBUF) + sz);
	ib->i_bufsz = sz;
	ib->i_ln = 0;
	ib->i_half = 0;

	return ib;
}
// }}}

void i2cb_clear(I2CBUF *sb) {
	// {{{
	sb->i_ln = 0;
	sb->i_half = 0;
}
// }}}

void i2cb_append(I2CBUF *ib, char c) {
	// {{{
	assert(ib->i_ln + 1 < ib->i_bufsz);

	if (ib->i_half) {
		ib->i_b[ib->i_ln-1] |= c & 0x0f;
		ib->i_half = 0;
	} else {
		ib->i_b[ib->i_ln++] = (c & 0x0f) << 4;
		ib->i_half = 1;
	}
}
// }}}

void i2cb_noop(I2CBUF *ib) {
	// {{{
	i2cb_append(ib, I2CB_NOOP);
}
// }}}

void i2cb_start(I2CBUF *ib) {
	// {{{
	i2cb_append(ib, I2CB_START);
}
// }}}

void i2cb_stop(I2CBUF *ib) {
	// {{{
	i2cb_append(ib, I2CB_STOP);
}
// }}}

void i2cb_addr(I2CBUF *ib, int addr) {
	// {{{
	i2cb_start(ib);
	i2cb_sendc(ib, addr);
}
// }}}

void i2cb_read(I2CBUF *ib, int ln) {
	// {{{
	if (ln == 0)
		return;

	assert(ib->i_ln + 2*((ln+255)/256) < ib->i_bufsz);

	while(ln > 256) {
		if (ib->i_half)
			ib->i_b[ib->i_ln-1] |= I2CB_READ;
		else
			ib->i_b[ib->i_ln++]  = I2CB_READ;
		ib->i_half = 0;
		ib->i_b[ib->i_ln++]  = 0xff;
		ln -= 256;
	} if (ln <= 16) {	// LN will *NOT* be zero here
		if (ib->i_half) {
			ib->i_b[ib->i_ln-1] |= I2CB_RNAK;
			ib->i_b[ib->i_ln++]  = ln-1;
		} else
			ib->i_b[ib->i_ln++]  = (I2CB_RNAK << 4) | (ln-1);
		ib->i_half = 0;
	} else if (ln > 0) {
		if (ib->i_half)
			ib->i_b[ib->i_ln-1] |= I2CB_RNAK;
		else
			ib->i_b[ib->i_ln++]  = I2CB_RNAK;
		ib->i_half = 0;
		ib->i_b[ib->i_ln++]  = (ln-1);
	}
}
// }}}

void i2cb_rdlast(I2CBUF *ib, int ln) {
	// {{{
	if (ln == 0)
		return;

	assert(ib->i_ln + 2*((ln+255)/256) < ib->i_bufsz);

	while(ln > 256) {
		if (ib->i_half)
			ib->i_b[ib->i_ln-1] |= I2CB_READ;
		else
			ib->i_b[ib->i_ln++]  = I2CB_READ;
		ib->i_half = 0;
		ib->i_b[ib->i_ln++]  = 0xff;
		ln -= 256;
	} if (ln <= 16) {	// LN will *NOT* be zero here
		if (ib->i_half) {
			ib->i_b[ib->i_ln-1] |= I2CB_RLAST;
			ib->i_b[ib->i_ln++]  = ln-1;
		} else
			ib->i_b[ib->i_ln++]  = (I2CB_RLAST << 4) | (ln-1);
		ib->i_half = 0;
		ln = 0;
	} else if (ln > 0) {
		if (ib->i_half)
			ib->i_b[ib->i_ln-1] |= I2CB_RLAST;
		else
			ib->i_b[ib->i_ln++]  = I2CB_RLAST;
		ib->i_half = 0;
		ib->i_b[ib->i_ln++]  = (ln-1);
		ln -= 256;
	}
}
// }}}

void i2cb_send(I2CBUF *ib, int ln, char *b) {
	// {{{
	// for(int k=0; k<ln; k++)
	//	i2cb_sendc(ib, b[k]);
	if (ln == 0)
		return;

	assert(ib->i_ln + 2*((ln+255)/256) + ln < ib->i_bufsz);

	while(ln > 256) {
		if (ib->i_half)
			ib->i_b[ib->i_ln-1] |= I2CB_SEND;
		else
			ib->i_b[ib->i_ln++]  = I2CB_SEND;
		ib->i_half = 0;
		ib->i_b[ib->i_ln++]  = 0xff;
		ln -= 256;

		for(int k=0; k<256; k++)
			ib->i_b[ib->i_ln++] = b[k];
	} if (ln <= 16) {	// LN will *NOT* be zero here
		if (ib->i_half) {
			ib->i_b[ib->i_ln-1] |= I2CB_SEND;
			ib->i_b[ib->i_ln++]  = ln-1;
		} else
			ib->i_b[ib->i_ln++]  = (I2CB_SEND << 4) | (ln-1);

		for(int k=0; k<ln; k++)
			ib->i_b[ib->i_ln++] = b[k];
		ib->i_half = 0;
		ln = 0;
	} else if (ln > 0) {
		if (ib->i_half)
			ib->i_b[ib->i_ln-1] |= I2CB_SEND;
		else
			ib->i_b[ib->i_ln++]  = I2CB_SEND;
		ib->i_half = 0;
		ib->i_b[ib->i_ln++]  = (ln-1);
		for(int k=0; k<ln; k++)
			ib->i_b[ib->i_ln++] = b[k];
		ln = 0;
	}
}
// }}}

void i2cb_sendc(I2CBUF *ib, char ch) {
	// {{{
	assert(ib->i_ln + 2 < ib->i_bufsz);
	i2cb_send(ib, 1, &ch);
}
// }}}

void i2cb_wait(I2CBUF *ib) {
	// {{{
	i2cb_append(ib, I2CB_WAIT);
}
// }}}

void i2cb_halt(I2CBUF *ib) {
	// {{{
	i2cb_append(ib, I2CB_HALT);
}
// }}}

void i2cb_target(I2CBUF *ib) {
	// {{{
	i2cb_append(ib, I2CB_TARGET);
}
// }}}

void i2cb_jump(I2CBUF *ib) {
	// {{{
	i2cb_append(ib, I2CB_JUMP);
}
// }}}

void	i2cb_channel(I2CBUF *ib, int ch) {
	// {{{
	if (ch < 16 && !ib->i_half) {
		ib->i_b[ib->i_ln++] = (I2CB_CHANNEL << 4) | ch;
	} else {
		if (ib->i_half) {
			ib->i_b[ib->i_ln-1] &= 0x0f0;
			ib->i_b[ib->i_ln-1] |= I2CB_CHANNEL;
		} else {
			ib->i_b[ib->i_ln++] = I2CB_CHANNEL;
		} ib->i_b[ib->i_ln++] = ch;
	} ib->i_half = 0;
}
// }}}
