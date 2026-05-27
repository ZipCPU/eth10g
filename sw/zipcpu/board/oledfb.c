////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/oledfb.c
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
#include <txfns.h>
#include <stdio.h>
#include <ctype.h>
#include <zipcpu.h>
#include "board.h"
#include "oledfont.h"
#include "oledfb.h"
#include "spibuf.h"
// }}}

OLEDFONT	*fb_font;
OLED_FB	*fb;
SPIBUF	*sb = NULL;
static const unsigned SPIC_STOPPED = 1;

void oled_init(void) {
	// {{{
	unsigned sz = sizeof(OLED_FB) + 128*4 - 1;

	fb = (OLED_FB *)malloc(sz);
#ifdef	_BOARD_HAS_OLEDBW
	fb->dev = (OLEDBW *)_oled;
#else
	fb->dev = NULL;
#endif
	fb->W = 128;
	fb->H = 4;
	fb->wrap = 0;
	fb->dirty = 0;

	oled_clear();
}
// }}}

void oled_hwsetup(void) {
	// {{{
	char	cmdbuf[48];

	oled_init();
	if (NULL == sb) {
		unsigned sz = 64 + 33 * ((fb->W * fb->H + 31)/32);
		sb = spib_new(sz);
		if (NULL == sb) {
			txstr("ERROR: SPIBUF Alloc failed!\n");
			zip_break();
		}
	}

	spib_start(sb, 0);
	cmdbuf[ 0] = 0xae;	// Display off
	cmdbuf[ 1] = 0xd5;	// Set display clockdiv
	cmdbuf[ 2] = 0x80;
	cmdbuf[ 3] = 0xa8;	// Set multiplex ratio
	cmdbuf[ 4] = 31;	//   Height - 1
	cmdbuf[ 5] = 0xd3;	// Display offset
	cmdbuf[ 6] = 0x00;	//   Offset = 0
	cmdbuf[ 7] = 0x40;	// Display start line = 0
	cmdbuf[ 8] = 0x8d;	// Charge pump = 0x14 (Internal VCC)
	cmdbuf[ 9] = 0x14;	//   0x10 for a 3.3V internal source
	cmdbuf[10] = 0x20;	// Memory mode
	cmdbuf[11] = 0x01;	//   Vertical addressing mode
	cmdbuf[12] = 0xa0;	//   SEGREMAP: Col0 mapd to seg0
	cmdbuf[13] = 0xc0;	//   COMSCANDEC: Map COM0 to COM31
	cmdbuf[14] = 0xda;	// Set compins = 0x02
	cmdbuf[15] = 0x02;	//   Sequential COM, disable lft/rht remap
	cmdbuf[16] = 0x81;	// Set contrast = 0x8f
	cmdbuf[17] = 0x8f;	//   New contrast
	cmdbuf[18] = 0xd9;	// Set precharge = 0xf1
	cmdbuf[19] = 0xf1;	//   New precharge
	cmdbuf[20] = 0xdb;	// Set SETVCOMDETECT
	cmdbuf[21] = 0x40;	//   Comm deselect = (not given)
	cmdbuf[22] = 0xa4;	// DISPLAYALLON_RESUME
	cmdbuf[23] = 0xa6;	// Normal Display
	cmdbuf[24] = 0x2e;	// Deactivate scroll
	cmdbuf[25] = 0x20;	// Set memory addressing mode
	cmdbuf[26] = 0x00;	//   Horizontal addressing mode
	cmdbuf[27] = 0x21;	// Set column address
	cmdbuf[28] = 0x00;	//   Column start address = 0
	cmdbuf[29] = 0x7f;	//   Column end address = 127
	cmdbuf[30] = 0x22;	// Set page start and end address
	cmdbuf[31] = 0x00;	//   Page start address = 00
	cmdbuf[32] = 0x03;	//   Page end address = 3 (i.e. 32bits high)
	spib_send(sb, 33, cmdbuf);
	spib_stop(sb);
	spib_start(sb, 1);	// Initiate a data transaction
	cmdbuf[0] = 0;
	// for(int k=0; k<128*4; k++)
	//	// Set the initial screen to all black
	//	spib_sendc(sb, 0);
	for(int i=0; i<fb->H * fb->W; i++)
		fb->b[i] = 0;
	spib_send(sb, fb->H * fb->W, fb->b);
	spib_stop(sb);
	spib_start(sb, 0);
	cmdbuf[0] = 0xa6;	// Normal display
	cmdbuf[1] = 0xaf;	// Turn the display on
	spib_send(sb, 2, cmdbuf);
	spib_stop(sb);
	spib_halt(sb);

	while(oled_busy())
		;	// Shouldn't be busy, but check anyway
	fb->dev->o_addr = (unsigned)&sb->i_b;
}
// }}}

void oled_clear(void) {
	// {{{
	for(int i=0; i<fb->H * fb->W; i++)
		fb->b[i] = 0;
	fb->x = 0; fb->y = 0;
	fb->dirty = 1;
}
// }}}

void oled_clear_eol(void) {
	// {{{
	int	lines = (fb_font) ? fb_font->m_height : 1;

	for(int yv=fb->y; yv< fb->y + lines && yv < fb->H; yv++) {
		char *sp = &fb->b[yv * fb->W];
		for(int xv=fb->x; xv < fb->W; xv++)
			sp[xv] = 0;
	}
	fb->dirty = 1;
}
// }}}

void oled_scroll(int count) {
	// {{{
	char *p;
	int	dW;
	if (count >= fb->H) {
		oled_clear();
	} else if (count > 0) {
		dW = count * fb->W;

		for(int j=0; j < fb->H-count; j++) {
			p = &fb->b[j*fb->W];

			for(int k=0; k < fb->W; k++)
				p[k] = p[k+dW];
		}

		for(int j=fb->H-count; j < fb->H; j++) {
			p = &fb->b[j*fb->W];
			for(int k=0; k < fb->W; k++)
				*p++ = 0;
		}

		fb->dirty = 1;
	}

	fb->x = 0;
}
// }}}

void oled_move(int x, int y) {
	// {{{
	int	lines = (fb_font) ? fb_font->m_height : 1;
	if (lines <= 1)
		lines = 1;
	if (lines >= fb->H)
		lines = fb->H - 1;

	fb->x = x;
	fb->y = y;
	if (x >= fb->W) {
		fb->x = 0;
		fb->y += fb_font->m_height;
	} if (fb->y <= 0) {
		fb->y = 0;
	} else if (fb->y >= fb->H - lines) {
		int	count = fb->y - (fb->H - lines);
		oled_scroll(count);

		fb->y = fb->H - lines;
	}
}
// }}}

char	flip(char k) {
	// {{{
	char	v = 0;

	if (k & 0x01) v |= 0x80;
	if (k & 0x02) v |= 0x40;
	if (k & 0x04) v |= 0x20;
	if (k & 0x08) v |= 0x10;

	if (k & 0x10) v |= 0x08;
	if (k & 0x20) v |= 0x04;
	if (k & 0x40) v |= 0x02;
	if (k & 0x80) v |= 0x01;

	return v;
}
// }}}

void oled_char(const char ch) {
	// {{{
	if (!fb_font)
		return;

	int	pre, post, w, lines;
	const char	*g;

	if (fb->y > fb->H - lines) {
		oled_scroll(fb->y - (fb->H - lines));
		fb->y = fb->H - lines;
	}

	g = fb_font->m_datp[ch];
	lines = fb_font->m_height;
	if ('\n' == ch) {
		oled_clear_eol();

		fb->y += lines;
		fb->x = 0;
	} else if ('\r' == ch) {
		fb->x = 0;
	} if (!g)
		return;

	w = fb_font->m_ln[ch] / lines;
	if (0 == w)
		return;

	if (fb_font->m_fixed && w < fb_font->m_fixed) {
		// Fixed width
		post  = fb_font->m_fixed - w;
		pre   = post/2;
		post -= pre;
	} else {
		pre = post = 0;
	}

	if (fb->wrap && fb->x >= fb->W) {
		fb->x = 0;
		fb->y++;
	} if (fb->y > fb->H - lines) {
		oled_scroll(fb->y - (fb->H - lines));
		fb->y = fb->H - lines;
	}
	for(int ln=0; ln<lines; ln++) {
		char *lp = &fb->b[(fb->y + ln) * fb->W];
		const char *fp = &g[w * ln];
		int	xs = fb->x;

		for(int x=xs; x < xs + pre && x < fb->W; x++)
			lp[x] = 0;
		xs += pre;
		for(int x=xs; x < xs + w && x < fb->W; x++)
			lp[x] = *fp++; // flip(*fp++);
		xs += w;
		for(int x=xs; x < xs + post && x < fb->W; x++)
			lp[x] = 0;
	} fb->x += w + pre + post;
	fb->dirty = 1;
}
// }}}

void oled_write(const char *str) {
	// {{{
	const char	*s = str;
	while(*s)
		oled_char(*s++);
}
// }}}

void oled_flush(void) {
	// {{{
	char	cmdbuf[16];

	if (0 == fb->dirty)
		return;
	if (NULL == fb || NULL == fb->dev) {
		txstr("ERROR: No OLED device\n");
		return;
	} if (NULL == sb) {
		sb = spib_new(64 + 33 * ((fb->W * fb->H + 31)/32));
		if (NULL == sb) {
			txstr("ERROR: SPIBUF Alloc failed!\n");
			return;
		}
	}

	if (fb->dev->o_cmd & SPIC_STOPPED) {
		// {{{
		spib_clear(sb);
		spib_start(sb, 0);
		// Set memory addressing mode
		// cmdbuf[0] = 0x20;	// But we're always in ...
		// cmdbuf[1] = 0x00;	// Horizontal addressing mode
		// Set column address (0x21)
		cmdbuf[0] = 0x21;
		cmdbuf[1] = 0x00;	// Column start address = 0
		cmdbuf[2] = 0x7f;	// Column end   address = 127 (0x3f)
		// Set page address (0x22)
		cmdbuf[3] = 0x22;	// Set page start & end address
		cmdbuf[4] = 0x00;	// Page start address = 0
		cmdbuf[5] = 0x03;	// Page end   address = 3
		// Now ... send the command buffer
		spib_send(sb, 6, cmdbuf);
		spib_stop(sb);
		spib_start(sb, 1);
		spib_send(sb, fb->W * fb->H, fb->b);
		spib_halt(sb);

		fb->dev->o_addr = (unsigned)&sb->i_b;

		fb->dirty = 0;
	}
	// }}}
}
// }}}

int	oled_busy(void) {
	// {{{
	if (NULL == fb || NULL == fb->dev)
		return 0;

	if (fb->dev->o_cmd & SPIC_STOPPED)
		return 0;
	return 1;
}
// }}}
