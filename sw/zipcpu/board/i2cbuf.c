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
	// RLSTNAK	6
#define	I2CB_RLAST	7
#define	I2CB_WAIT	8
#define	I2CB_HALT	9
#define	I2CB_ABORT	10
#define	I2CB_TARGET	11
#define	I2CB_JUMP	12
#define	I2CB_CHANNEL	13

/*
typedef	struct	I2CBUF_S {
	int	i_ln, i_bufsz, i_half, i_stopped;
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
		ib->i_b[ib->i_ln++] = c & 0x0f;
		ib->i_half = 0;
	} else {
		ib->i_b[ib->i_ln] = (c & 0x0f) << 4;
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

	for(int k=0; k<ln-1; k++)
		i2cb_append(ib, I2CB_READ);
	i2cb_append(ib, I2CB_RNAK);
}
// }}}

void i2cb_rdlast(I2CBUF *ib, int ln) {
	// {{{
	if (ln == 0)
		return;

	for(int k=0; k<ln-1; k++)
		i2cb_append(ib, I2CB_READ);
	i2cb_append(ib, I2CB_RLAST);
}
// }}}

void i2cb_send(I2CBUF *ib, int ln, char *b) {
	// {{{
	for(int k=0; k<ln; k++)
		i2cb_sendc(ib, b[k]);
}
// }}}

void i2cb_sendc(I2CBUF *ib, char ch) {
	// {{{
	assert(ib->i_ln + 2 < ib->i_bufsz);
	i2cb_append(ib, I2CB_SEND);
	ib->i_half = 0;

	ib->i_b[ib->i_ln++] = ch;
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
	i2cb_append(ib, I2CB_CHANNEL);
	ib->i_half = 0;
	ib->i_b[ib->i_ln++] = ch;
}
// }}}
