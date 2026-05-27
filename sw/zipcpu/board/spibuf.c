////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/spibuf.c
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
#include <txfns.h>
#include <stdio.h>
#include "spibuf.h"
// }}}

#define	SPIB_START	0
#define	SPIB_STOP	0x1f
#define	SPIB_READ	0x20
#define	SPIB_SEND	0x40
#define	SPIB_TXRX	0x60
#define	SPIB_LAST	0x80
#define	SPIB_HALT	0xa0
#define	SPIB_WAIT	0xa8
#define	SPIB_TICK	0xb0
#define	SPIB_TICKS	SPIB_TICK
#define	SPIB_TARGET	0xc0
#define	SPIB_JUMP	0xc8
#define	SPIB_CHANNEL	0xe0
#define	SPIB_NOOP	0xff

/*
typedef	struct	SPIBUF_S {
	int	i_ln, i_bufsz, i_half, i_stopped;
	char	i_b[1];
} SPIBUF;
*/

SPIBUF *spib_new(int sz) {
	// {{{
	SPIBUF	*sb;

	sz += 3;
	sz &= ~0x03;
	sb = malloc(sizeof(SPIBUF) + sz);
	sb->i_bufsz = sz;
	sb->i_ln = 0;
	sb->i_stopped = 1;

	return sb;
}
// }}}

void spib_clear(SPIBUF *sb) {
	// {{{
	sb->i_ln = 0;
	sb->i_stopped = 1;
	sb->i_lastp = 0;
}
// }}}

void spib_append(SPIBUF *b, char c) {
	// {{{
	assert(b->i_ln + 1 < b->i_bufsz);
	b->i_b[b->i_ln++] = c;
}
// }}}

void spib_start(SPIBUF *sb, char ch) {
	// {{{
	spib_append(sb, SPIB_START | (ch & 0x1f));
	sb->i_stopped = 0;
	sb->i_lastp = sb->i_ln;
}
// }}}

void spib_stop(SPIBUF *sb) {
	// {{{
	spib_append(sb, SPIB_STOP);
	sb->i_stopped = 1;
	sb->i_lastp = sb->i_ln;
}
// }}}

void spib_read(SPIBUF *sb, int ln) {
	// {{{
	int	k = ln;

	if((sb->i_lastp < sb->i_ln)
			&& (SPIB_READ == (sb->i_b[sb->i_lastp] & 0xe0))
			&& (0x1f != (sb->i_b[sb->i_lastp] & 0x1f))) {
		int	ch = sb->i_b[sb->i_lastp];
		int	av = 0x20 - (ch & 0x1f);

		av = 0x20 - av;
		if (k <= av) {
			av = ch + k;
			av &= 0x1f;
			ch = (ch & 0xe0) | (av & 0x1f);
			sb->i_b[sb->i_lastp] = ch;
			k = 0;
		} else {
			sb->i_b[sb->i_lastp] |= 0x1f;
			k -= av;
		}
	} while(k >= 0x20) {
		spib_append(sb, SPIB_READ | 0x1f);
	} if (k > 0)
		spib_append(sb, SPIB_READ | ((k-1) & 0x1f));
	sb->i_lastp = sb->i_ln-1;
}
// }}}

void spib_send(SPIBUF *sb, int ln, char *b) {
	// {{{
	int	k = ln;

	if((sb->i_lastp < sb->i_ln)
			&& (SPIB_SEND == (sb->i_b[sb->i_lastp] & 0xe0))
			&& (0x1f != (sb->i_b[sb->i_lastp] & 0x1f))) {
		int	ch = sb->i_b[sb->i_lastp];
		int	av = 0x20 - (ch & 0x1f);

		av = 0x20 - av;
		if (k <= av) {
			av = ch + k;
			av &= 0x1f;
			ch = (ch & 0xe0) | (av & 0x1f);
			sb->i_b[sb->i_lastp] = ch;
			for(int s=0; s < k; s++)
				spib_append(sb, *b++);
			k = 0;
		} else {
			sb->i_b[sb->i_lastp] |= 0x1f;
			for(int s=0; s < av; s++)
				spib_append(sb, *b++);
			k -= av;
		}
	} while(k >= 0x20) {
		spib_append(sb, SPIB_SEND | 0x1f);
		sb->i_lastp = sb->i_ln-1;
		for(int s=0; s < 0x20; s++) {
			spib_append(sb, *b++);
		} k -= 0x20;
		
	} if (k > 0) {
		spib_append(sb, SPIB_SEND | ((k-1) & 0x1f));
		sb->i_lastp = sb->i_ln-1;
		for(int s=0; s < k; s++) {
			spib_append(sb, *b++);
		}
	}
}
// }}}

void spib_sendc(SPIBUF *sb, char ch) {
	// {{{
	char	buf[4];
	buf[0] = ch;
	spib_send(sb, 1, buf);
}
// }}}

void spib_txrx(SPIBUF *sb, int ln, char *b) {
	// {{{
	int	k = ln;

	if((sb->i_lastp < sb->i_ln)
			&& (SPIB_TXRX == (sb->i_b[sb->i_lastp] & 0xe0))
			&& (0x1f != (sb->i_b[sb->i_lastp] & 0x1f))) {
		int	ch = sb->i_b[sb->i_lastp];
		int	av = 0x20 - (ch & 0x1f);

		av = 0x20 - av;
		if (k <= av) {
			av = ch + k;
			av &= 0x1f;
			ch = (ch & 0xe0) | (av & 0x1f);
			sb->i_b[sb->i_lastp] = ch;
			for(int s=0; s < k; s++)
				spib_append(sb, *b++);
			k = 0;
		} else {
			sb->i_b[sb->i_lastp] |= 0x1f;
			for(int s=0; s < av; s++)
				spib_append(sb, *b++);
			k -= av;
		}
	} while(k >= 0x20) {
		spib_append(sb, SPIB_TXRX | 0x1f);
		sb->i_lastp = sb->i_ln-1;
		for(int s=0; s < 0x20; s++) {
			spib_append(sb, *b++);
		} k -= 0x20;
	} if (k > 0) {
		spib_append(sb, SPIB_TXRX | ((k-1) & 0x1f));
		sb->i_lastp = sb->i_ln-1;
		for(int s=0; s < k; s++) {
			spib_append(sb, *b++);
		}
	}
}
// }}}

void spib_txrxc(SPIBUF *sb, char ch) {
	// {{{
	char	buf[4];
	buf[0] = ch;
	spib_txrx(sb, 1, buf);
}
// }}}

void spib_last(SPIBUF *sb) {
	// {{{
	spib_append(sb, SPIB_LAST);
	sb->i_lastp = sb->i_ln;
}
// }}}

void spib_wait(SPIBUF *sb) {
	// {{{
	spib_append(sb, SPIB_WAIT);
	sb->i_lastp = sb->i_ln;
}
// }}}

void spib_halt(SPIBUF *sb) {
	// {{{
	spib_append(sb, SPIB_HALT);
	sb->i_lastp = sb->i_ln;
}
// }}}

void spib_ticks(SPIBUF *sb, int count) {
	// {{{
	while(count > 15) {
		spib_append(sb, SPIB_TICKS | 0x1f);
		count -= 16;
	} if (count > 0)
		spib_append(sb, SPIB_TICKS | ((count - 1) & 0x0f));
	sb->i_lastp = sb->i_ln;
}
// }}}

void spib_target(SPIBUF *sb) {
	// {{{
	spib_append(sb, SPIB_TARGET);
	sb->i_lastp = sb->i_ln;
}
// }}}

void spib_jump(SPIBUF *sb) {
	// {{{
	spib_append(sb, SPIB_JUMP);
	sb->i_lastp = sb->i_ln;
}
// }}}

void spib_channel(SPIBUF *sb, int ch) {
	// {{{
	spib_append(sb, SPIB_CHANNEL | (ch & 0x0f));
	sb->i_lastp = sb->i_ln;
}
// }}}

