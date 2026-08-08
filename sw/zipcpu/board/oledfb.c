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
#include <stdio.h>
#include <ctype.h>
#include <zipcpu.h>
#include "txfns.h"
#include "board.h"
#include "oledfont.h"
#include "oledfb.h"
#include "i2cbuf.h"
// }}}

const unsigned	I2CMUX_ADDR	= 0xe8,
		I2CMUX_WR	= 0,
		// I2CMUX_RD	= 1,
		I2CMUX_OLED	= 0x04, // 0x86 ? 0x07 ?
		OLED_ADDR	= 0x78,
		OLED_CONTROL	= 0x80,
		OLED_DATA	= 0x40;

OLEDFONT	*fb_font;
OLED_FB	*fb;
I2CBUF	*sb = NULL;

#ifdef	_BOARD_HAS_I2CSCOPE
#define	I2C_SET_SCOPE		_i2cscope->s_ctrl = 0x04000100
#define	I2C_TRIGGER_SCOPE	_i2cscope->s_ctrl = 0xff000100
#else
#define	I2C_SET_SCOPE
#define	I2C_TRIGGER_SCOPE
#endif

void oled_init(void) {
	// {{{
	unsigned sz = sizeof(OLED_FB) + 128*4 - 1;
	fb = (OLED_FB *)malloc(sz);
#ifdef	_BOARD_HAS_I2CCPU
	fb->dev = (I2CCPU *)_i2c;
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
	char	cmdbuf[96];

	I2C_SET_SCOPE;
	oled_init();
	if (NULL == sb) {
		unsigned sz = 2*68 + 2 * 33 * ((fb->W * fb->H + 31)/32);
		sb = i2cb_new(sz);
		if (NULL == sb) {
			txstr("ERROR: I2CBUF Alloc failed!\n");
			zip_break();
		}
	}

	i2cb_clear(sb);
	i2cb_start(sb);
	i2cb_addr(sb,  I2CMUX_ADDR|I2CMUX_WR);
	i2cb_sendc(sb, I2CMUX_OLED);
	i2cb_stop(sb);
	i2cb_start(sb);
	i2cb_addr(sb,  OLED_ADDR|I2CMUX_WR);

	cmdbuf[ 0] = OLED_CONTROL;
	cmdbuf[ 1] = 0xae;	// Display off
	cmdbuf[ 2] = OLED_CONTROL;
	cmdbuf[ 3] = 0xd5;	// Set display clockdiv
	cmdbuf[ 4] = OLED_CONTROL;
	cmdbuf[ 5] = 0x80;
	cmdbuf[ 6] = OLED_CONTROL;
	cmdbuf[ 7] = 0xa8;	// Set multiplex ratio
	cmdbuf[ 8] = OLED_CONTROL;
	cmdbuf[ 9] = 0x1f;	//	= Height - 1
	cmdbuf[10] = OLED_CONTROL;
	cmdbuf[11] = 0xd3;	// Display offset
	cmdbuf[12] = OLED_CONTROL;
	cmdbuf[13] = 0x00;	//   Offset = 0
	cmdbuf[14] = OLED_CONTROL;
	cmdbuf[15] = 0x40;	// Display start line = 0
	cmdbuf[16] = OLED_CONTROL;
	cmdbuf[17] = 0x8d;	// Charge pump = 0x14 (Internal VCC)
	cmdbuf[18] = OLED_CONTROL;
	cmdbuf[19] = 0x14;	//   0x10 for a 3.3V internal source
	cmdbuf[20] = OLED_CONTROL;
	cmdbuf[21] = 0x20;	// Memory mode
	cmdbuf[22] = OLED_CONTROL;
	cmdbuf[23] = 0x01;	//   Vertical addressing mode
	cmdbuf[24] = OLED_CONTROL;
	cmdbuf[25] = 0xa0;	//   SEGREMAP: Col0 mapd to seg0
	cmdbuf[26] = OLED_CONTROL;
	cmdbuf[27] = 0xc0;	//   COMSCANDEC: Map COM0 to COM31
	cmdbuf[28] = OLED_CONTROL;
	cmdbuf[29] = 0xda;	// Set compins = 0x02
	cmdbuf[30] = OLED_CONTROL;
	cmdbuf[31] = 0x02;	//   Sequential COM, disable lft/rht remap
	cmdbuf[32] = OLED_CONTROL;
	cmdbuf[33] = 0x81;	// Set contrast = 0x8f
	cmdbuf[34] = OLED_CONTROL;
	cmdbuf[35] = 0x8f;	//   New contrast
	cmdbuf[36] = OLED_CONTROL;
	cmdbuf[37] = 0xd9;	// Set precharge = 0xf1
	cmdbuf[38] = OLED_CONTROL;
	cmdbuf[39] = 0xf1;	//   New precharge
	cmdbuf[40] = OLED_CONTROL;
	cmdbuf[41] = 0xdb;	// Set SETVCOMDETECT
	cmdbuf[42] = OLED_CONTROL;
	cmdbuf[43] = 0x40;	//   Comm deselect = (not given)
	cmdbuf[44] = OLED_CONTROL;
	cmdbuf[45] = 0xa4;	// DISPLAYALLON_RESUME
	cmdbuf[46] = OLED_CONTROL;
	cmdbuf[47] = 0xa6;	// Normal Display
	cmdbuf[48] = OLED_CONTROL;
	cmdbuf[49] = 0x2e;	// Deactivate scroll
	cmdbuf[50] = OLED_CONTROL;
	cmdbuf[51] = 0x20;	// Set memory addressing mode
	cmdbuf[52] = OLED_CONTROL;
	cmdbuf[53] = 0x00;	//   Horizontal addressing mode	[ LOGO->Vert,1 ]
	cmdbuf[54] = OLED_CONTROL;
	cmdbuf[55] = 0x21;	// Set column address
	cmdbuf[56] = OLED_CONTROL;
	cmdbuf[57] = 0x00;	//   Column start address = 0
	cmdbuf[58] = OLED_CONTROL;
	cmdbuf[59] = 0x7f;	//   Column end address = 127
	cmdbuf[60] = OLED_CONTROL;
	cmdbuf[61] = 0x22;	// Set page start and end address
	cmdbuf[62] = OLED_CONTROL;
	cmdbuf[63] = 0x00;	//   Page start address = 00
	cmdbuf[64] = OLED_CONTROL;
	cmdbuf[65] = 0x03;	//   Page end address = 3 (i.e. 32bits high)
	i2cb_send(sb, 66, cmdbuf);
	// for(int k=0; k<128*4; k++)
	//	// Set the initial screen to all black
	//	i2cb_sendc(sb, 0);
	for(int i=0; i<fb->H * fb->W; i++)
		fb->b[i] = 0;
	i2cb_start(sb);	// Initiate a data transaction
	i2cb_addr(sb,  OLED_ADDR|I2CMUX_WR);
	i2cb_sendc(sb, OLED_DATA);	// All data, from here on out
	i2cb_send(sb, fb->H * fb->W, fb->b);
	i2cb_start(sb);
	i2cb_addr(sb,  OLED_ADDR|I2CMUX_WR);
	cmdbuf[0] = OLED_CONTROL;
	cmdbuf[1] = 0xa6;	// Normal display	[ Inverse in logo ]
	cmdbuf[2] = OLED_CONTROL;
	cmdbuf[3] = 0xaf;	// Turn the display on
	i2cb_send(sb, 4, cmdbuf);
	i2cb_stop(sb);
	i2cb_halt(sb);

	if (oled_busy())
		fb->dev->ic_control = I2CC_HALT;
	while(oled_busy())
		;	// Shouldn't be busy, but check anyway
	if (fb->dev->ic_control & I2CC_FAULT)
		fb->dev->ic_control = I2CC_FAULT;	// Clear any errors

	// extern void i2cb_dump(I2CBUF *);
	// i2cb_dump(sb);

	fb->dev->ic_address = (unsigned)&sb->i_b;
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
		oled_clear_eol();
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
		sb = i2cb_new(96 + 33 * ((fb->W * fb->H + 31)/32));
		if (NULL == sb) {
			txstr("ERROR: I2CBUF Alloc failed!\n");
			return;
		}
	} // oled_dump();

	if (fb->dev->ic_control & I2CC_STOPPED) {
		// {{{
		if (fb->dev->ic_control & I2CC_FAULT) {
			I2C_TRIGGER_SCOPE;
			txstr("ERROR: I2C failed on fault: 0x");
			txhex(fb->dev->ic_control);
			txstr("\n");
			fb->dev->ic_control = I2CC_ABORT | I2CC_ERROR;
		} // else txstr("Setting I2C\n");
		i2cb_clear(sb);
		i2cb_start(sb);
		i2cb_addr(sb,  I2CMUX_ADDR|I2CMUX_WR);
		i2cb_sendc(sb, I2CMUX_OLED);
		i2cb_stop(sb);
		i2cb_start(sb);
		i2cb_addr(sb,  OLED_ADDR|I2CMUX_WR);
		// Set memory addressing mode
		// cmdbuf[0] = 0x20;	// But we're always in ...
		// cmdbuf[1] = 0x00;	// Horizontal addressing mode
		// Set column address (0x21)
		cmdbuf[ 0] = OLED_CONTROL;
		cmdbuf[ 1] = 0x21;
		cmdbuf[ 2] = OLED_CONTROL;
		cmdbuf[ 3] = 0x00;	// Column start address = 0
		cmdbuf[ 4] = OLED_CONTROL;
		cmdbuf[ 5] = 0x7f;	// Column end   address = 127 (0x3f)
		// Set page address (0x22)
		cmdbuf[ 6] = OLED_CONTROL;
		cmdbuf[ 7] = 0x22;	// Set page start & end address
		cmdbuf[ 8] = OLED_CONTROL;
		cmdbuf[ 9] = 0x00;	// Page start address = 0
		cmdbuf[10] = OLED_CONTROL;
		cmdbuf[11] = 0x03;	// Page end   address = 3
		// Now ... send the command buffer
		i2cb_send(sb, 12, cmdbuf);
		i2cb_start(sb);
		i2cb_addr(sb,  OLED_ADDR|I2CMUX_WR);
		i2cb_sendc(sb, OLED_DATA);
		i2cb_send(sb, fb->W * fb->H, fb->b);
		i2cb_stop(sb);
		i2cb_halt(sb);

		// i2cb_dump(sb);
		fb->dev->ic_address = (unsigned)&sb->i_b;

		fb->dirty = 0;
	} // else txstr("I2C Controller still busy ...\n");
	// }}}
}
// }}}

int	oled_busy(void) {
	// {{{
	if (NULL == fb || NULL == fb->dev)
		return 0;

	if (fb->dev->ic_control & I2CC_STOPPED)
		return 0;
	return 1;
}
// }}}

void	oled_dump(void) {
	// {{{
	for(int x=0; x< fb->W; x++) {
		for(int ln= fb->H-1; ln >= 0; ln--) {
			char *lp = &fb->b[ln * fb->W];
			unsigned p = lp[x];
			for(int b=0; b< 8; b++) {
				if (p & (1<<(7-b)))
					putchar('X');
				else
					putchar('.');
			}
		} putchar('\n');
	}
}
// }}}
