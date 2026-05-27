////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/oledtall.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:
//
// Designed based upon the PixelArmy Font
//
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
#include <stddef.h>
// }}}
#include "oledfont.h"

OLEDFONT	tallfont, *tallfontp;

extern	void	init_tall_glyfs(void);

static const char glyf_A[] = {
	// {{{
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 1 1 0 0 0
	// 0 0 0 0 1 1 0 0 0
	// 0 0 0 0 1 1 0 0 0
	// 0 0 0 0 0 1 1 0 0
	// 0 0 1 1 0 1 1 0 0
	// 0 0 1 1 0 1 1 0 0
	// 0 1 1 0 0 0 1 1 0
	0x00, 0x80, 0xe0, 0x60, 0x0e, 0x7e, 0xf0, 0x80, 0x00, 0x00,
	//+0 1 1 0 1 1 1 1 0
	// 0 1 1 0 1 1 1 1 0
	// 1 1 0 0 0 0 0 1 1
	// 1 1 0 0 0 0 0 1 1
	// 1 1 0 0 0 0 0 1 1
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	0x1c, 0x1f, 0x03, 0x00, 0x03, 0x03, 0x03, 0x1f, 0x1c, 0x00
};
// }}}

static const char glyf_B[] = {
	// {{{
	// 0 0 0 0 0 0 0 0 0
	// 1 1 0 1 1 1 1 0 0
	// 1 1 0 1 1 1 1 0 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 1 1 1 1 0 0
	// 1 1 0 1 1 1 1 0 0
	0xfe, 0xfe, 0x00, 0xc6, 0xc6, 0xc6, 0xfe, 0x38, 0x00,
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 1 1 1 1 1 0
	// 1 1 0 1 1 1 1 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	0x1f, 0x1f, 0x00, 0x18, 0x18, 0x18, 0x1f, 0x0f, 0x00
};
// }}}

static const char glyf_C[] = {
	// {{{
	// 0 0 0 0 0 0 0 0 0
	// 0 0 1 1 0 1 1 0 0
	// 0 1 1 1 0 1 1 1 0
	// 1 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 0 0 
	// 1 1 0 0 0 0 0 0 0 
	// 1 1 0 0 0 0 0 0 0 
	// 1 1 0 0 0 0 0 0 0 
	0xf8, 0xfc, 0x0e, 0x06, 0x00, 0x06, 0x0e, 0x0c, 0x00,
	// 1 1 0 0 0 0 0 0 0 
	// 1 1 0 0 0 0 0 0 0 
	// 1 1 1 0 0 0 1 1 0
	// 0 1 1 1 0 1 1 1 0
	// 0 0 1 1 0 1 1 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	0x07, 0x0f, 0x1c, 0x18, 0x00, 0x18, 0x1c, 0x1c, 0x00
};
// }}}

static const char glyf_D[] = {
	// {{{
	// 0 0 0 0 0 0 0 0 0
	// 1 1 0 1 1 1 0 0 0
	// 1 1 0 1 1 1 1 0 0
	// 1 1 0 0 0 1 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	0xfe, 0xfe, 0x00, 0x06, 0x06, 0x0e, 0xfc, 0xf8, 0x00,
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 1 0
	// 1 1 0 1 1 1 1 0 0
	// 1 1 0 1 1 1 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	0x1f, 0x1f, 0x00, 0x18, 0x18, 0x1c, 0x0f, 0x07, 0x00
};
// }}}

static const char glyf_E[] = {
	// {{{
	// 0 0 0 0 0 0 0 0
	// 1 1 0 1 1 1 1 0
	// 1 1 0 1 1 1 1 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 1 1 0 0 0 0
	// 1 1 1 1 0 0 0 0
	0xfe, 0xfe, 0xc0, 0x63, 0x06, 0x06, 0x06, 0x00,
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 1 1 1 1 0
	// 1 1 0 1 1 1 1 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	0x1f, 0x1f, 0x00, 0x18, 0x18, 0x18, 0x18, 0x00
};
// }}}

static const char glyf_F[] = {
	// {{{
	// 0 0 0 0 0 0 0 0
	// 1 1 0 1 1 1 1 0
	// 1 1 0 1 1 1 1 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 1 1 0 0 0 0
	// 1 1 1 1 0 0 0 0
	0xfe, 0xfe, 0xc0, 0x36, 0x06, 0x06, 0x06, 0x00,
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	0x1f, 0x1f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_G[] = {
	// {{{
	// 0 0 0 0 0 0 0 0 0
	// 0 0 1 1 0 1 1 0 0
	// 0 1 1 1 0 1 1 1 0
	// 1 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0 0
	// 1 1 0 0 1 1 1 1 0
	0xf8, 0xfc, 0x0e, 0x06, 0x80, 0x86, 0x8e, 0x8c, 0x00,
	// 1 1 0 0 1 1 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 1 0 0 0 1 1 0
	// 0 1 1 1 0 1 1 1 0
	// 0 0 1 1 0 1 1 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	0x07, 0x0f, 0x1c, 0x18, 0x01, 0x19, 0x1f, 0x0f, 0x00
};
// }}}

static const char glyf_H[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0
	// 1 1 0 0|0 0 0 1|1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 1 1 0 1 1 1 1 0
	// 1 1 1 1 0 1 1 1 1 0
	0xfe, 0xfe, 0xc0, 0xc0, 0x00, 0xc0, 0xc0, 0xfe, 0xfe, 0x00,
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	0x1f, 0x1f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1f, 0x1f, 0x00
};
// }}}

static const char glyf_I[] = {
	// {{{
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	0xfe, 0xfe, 0x00,
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	0x1f, 0x1f, 0x00
};
// }}}

static const char glyf_J[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	0x00, 0x00, 0x00, 0x00, 0x00, 0xfe, 0xfe, 0x00,
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 1 0 1 1 1 0
	// 0 1 1 0 1 1 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	0x0c, 0x1c, 0x18, 0x00, 0x18, 0x1f, 0x0f, 0x00
};
// }}}

static const char glyf_K[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 1 1 0 0
	// 1 1 0 0 1 1 0 0
	// 1 1 0 1 1 0 0 0
	// 1 1 0 1 1 0 0 0
	// 1 1 0 1 1 0 0 0
	0xfe, 0xfe, 0x00, 0xe0, 0xf8, 0x1e, 0x06, 0x00,
	// 1 1 0 0 1 1 0 0
	// 1 1 0 0 1 1 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x1f, 0x1f, 0x00, 0x00, 0x03, 0x1f, 0x1c, 0x00
};
// }}}

static const char glyf_L[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 1 1 0 0|0 0 0 0
	// 1 1 0 0|0 0 0 0
	// 1 1 0 0|0 0 0 0
	// 1 1 0 0|0 0 0 0
	// 1 1 0 0|0 0 0 0
	// 1 1 0 0|0 0 0 0
	// 1 1 0 0|0 0 0 0
	0xfe, 0xfe, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	// 1 1 0 0|0 0 0 0
	// 1 1 0 0|0 0 0 0
	// 1 1 0 0|0 0 0 0
	// 1 1 0 1|1 1 1 0
	// 1 1 0 1|1 1 1 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x1f, 0x1f, 0x00, 0x18, 0x18, 0x18, 0x18, 0x00
};
// }}}

static const char glyf_M[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 0 1 1 0 0 1 1 1 0
	// 0 1 1 0 0 1 1 1 0
	// 0 0 1 1 0 0 1 1 0
	// 1 0 1 1 0 0 1 1 0
	// 1 0 0 1 1 0 1 1 0
	0x36, 0x1e, 0x78, 0xe0, 0x80, 0x18, 0xfe, 0xfe, 0x00,
	// 1 0 0 1 1 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 0|0 0 0 0|0
	0x1f, 0x1e, 0x00, 0x01, 0x01, 0x00, 0x1f, 0x1f, 0x00
};
// }}}

static const char glyf_N[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 1 1 0 0 1 1 0
	// 0 1 1 0 0 1 1 0
	// 0 0 1 1 0 1 1 0
	// 1 0 1 1 0 1 1 0
	// 1 0 0 1 1 0 1 0
	0x36, 0x1e, 0x78, 0xe0, 0x80, 0x7e, 0xfe, 0x00,
	// 1 1 0 1 1 0 0 0
	// 1 1 0 0 1 1 0 0
	// 1 1 0 0 1 1 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x1f, 0x1f, 0x00, 0x01, 0x07, 0x1e, 0x18, 0x00
};
// }}}

static const char glyf_O[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 1 1 0 1 1 0 0 0
	// 0 1 1 1 0 1 1 1 0 0
	// 1 1 1 0 0 0 1 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	0xf8, 0xfc, 0x0e, 0x06, 0x00, 0x06, 0x0e, 0xfc, 0xf8, 0x00,
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 1 0 0 0 1 1 1 0
	// 0 1 1 1 0 1 1 1 0 0
	// 0 0 1 1 0 1 1 0 0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	0x07, 0x0f, 0x1c, 0x18, 0x00, 0x18, 0x1c, 0x0f, 0x07, 0x00
};
// }}}

static const char glyf_P[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 1 1 0 1 1 1 0 0
	// 1 1 0 1 1 1 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 1 1 1 1 0
	// 1 1 0 1 1 1 0 0
	0xfe, 0xfe, 0x00, 0x36, 0x36, 0xfe, 0x78, 0x00,
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	0x1f, 0x1f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_Q[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 1 1 0 1 1 0 0 0
	// 0 1 1 1 0 1 1 1 0 0
	// 1 1 1 0 0 0 1 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	0xf8, 0xfc, 0x0e, 0x06, 0x00, 0x06, 0x0e, 0xfc, 0xf8, 0x00,
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 1 0 0 1 1 1 1 0
	// 0 1 1 1 0 1 1 0 0 0
	// 0 0 1 1 0 1 1 1 0 0
	// 0 0 0 0|0 0 1 1|0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	0x07, 0x0f, 0x1c, 0x1c, 0x00, 0x1c, 0x3c, 0x37, 0x07, 0x00
};
// }}}

static const char glyf_R[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 1 1 0 1 1 1 0 0
	// 1 1 0 1 1 1 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 1 1 1 1 0
	// 1 1 0 1 1 1 0 0
	0xfe, 0xfe, 0x00, 0x36, 0x36, 0xfe, 0x78, 0x00,
	// 1 1 0 1 1 0 0 0
	// 1 1 0 0 1 1 0 0
	// 1 1 0 0 1 1 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x1f, 0x1f, 0x00, 0x01, 0x07, 0x1e, 0x18, 0x00
};
// }}}

static const char glyf_S[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 1 1 0 1 1 0 0
	// 1 1 1 0 1 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 0
	// 1 1 1 0 0 0 0 0
	// 0 1 1 1 1 0 0 0
	// 0 0 1 1 1 1 0 0
	0x3c, 0x7e, 0xe6, 0xc0, 0x36, 0x8e, 0x0c, 0x00,
	// 0 0 0 0 1 1 1 0
	// 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 1 0 1 1 1 0
	// 0 1 1 0 1 1 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x0c, 0x1c, 0x18, 0x00, 0x19, 0x1f, 0x0f, 0x00
};
// }}}

static const char glyf_T[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0
	// 1 1 1 1 1 1 1 1 0
	// 1 1 1 1 1 1 1 1 0
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	0x06, 0x06, 0x06, 0xf6, 0xf6, 0x06, 0x06, 0x06, 0x00,
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 0|0 0 0 0|0
	0x00, 0x00, 0x00, 0x1f, 0x1f, 0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_U[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	0xfe, 0xfe, 0x00, 0x00, 0x00, 0x00, 0x00, 0xfe, 0xfe, 0x00,
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 1 0 0 0 1 1 1 0
	// 0 1 1 1 0 1 1 1 0 0
	// 0 0 1 1 0 1 1 0 0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	0x07, 0x0f, 0x1c, 0x18, 0x00, 0x18, 0x1c, 0x0f, 0x07, 0x00
};
// }}}

static const char glyf_V[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 0 1 1 0 0 0 1 1 0 0
	// 0 1 1 0 0 0 1 1 0 0
	// 0 1 1 0 0 0 1 1 0 0
	// 0 0 1 1 0 1 1 0 0 0
	0x0e, 0x7e, 0xf0, 0x80, 0x00, 0x80, 0xf0, 0x7e, 0x0e, 0x00,
	// 0 0 1 1 0 1 1 0 0 0
	// 0 0 1 1 0 0 0 0 0 0
	// 0 0 0 1 1 0 0 0 0 0
	// 0 0 0 1 1 0 0 0 0 0
	// 0 0 0 1 1 0 0 0 0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	0x00, 0x00, 0x03, 0x1f, 0x1c, 0x01, 0x01, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_W[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0 0 0
	// 1 1 0 0 1 1 0 0 0 1 1 0
	// 1 1 0 0 1 1 0 0 0 1 1 0
	// 1 1 0 0 1 1 0 0 0 1 1 0

	// 1 1 0 0 1 1 0 0 0 1 1 0
	// 0 1 1 0 0 1 1 0 1 1 0 0
	// 0 1 1 0 0 1 1 0 1 1 0 0
	// 0 1 1 0 0 1 1 0 1 1 0 0
	0x1e, 0xfe, 0xe0, 0x00, 0x1e, 0xfe, 0xe0, 0x00, 0xe0, 0xfe, 0x1e, 0x00,
	// 0 1 1 0 0 1 1 0 0 0 0 0
	// 0 0 1 1 0 0 1 1 1 0 0 0
	// 0 0 1 1 1 0 1 1 1 0 0 0
	// 0 0 1 1 0 0 1 1 0 0 0 0

	// 0 0 1 1 0 0 1 1 0 0 0 0
	// 0 0 0 0|0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0|0 0 0 0
	0x00, 0x01, 0x1f, 0x1e, 0x04, 0x01, 0x1f, 0x1e, 0x06, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_X[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 1 1 0 1 1 0 0
	// 0 1 1 0 1 0 0 0
	// 0 0 1 1 0 0 0 0
	// 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0
	0x06, 0x1e, 0x78, 0xe0, 0x98, 0x0e, 0x06, 0x00,
	// 0 0 0 1 1 0 0 0
	// 0 1 0 0 1 1 0 0
	// 0 1 1 0 1 1 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x18, 0x1e, 0x04, 0x01, 0x07, 0x1e, 0x18, 0x00
};
// }}}

static const char glyf_Y[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0
	// 1 1 0 0 0 0 1 1 0
	// 1 1 0 0 0 0 1 1 0
	// 0 1 1 0 0 1 1 0 0
	// 0 1 1 0 0 1 1 0 0
	// 0 0 1 1 0 0 0 0 0
	// 0 0 1 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	0x06, 0x1e, 0x78, 0xe0, 0xc0, 0x18, 0x1e, 0x06, 0x00,
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 1 1 0 0 0 0
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 0|0 0 0 0|0
	0x00, 0x00, 0x00, 0x1f, 0x1f, 0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_Z[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 1 1 1 1 0 1 1 0
	// 1 1 1 0 0 1 1 0
	// 0 0 0 0 1 1 0 0
	// 0 0 0 0 1 1 0 0
	// 0 0 0 1 1 0 0 0
	// 0 0 0 1 1 0 0 0
	// 0 0 1 1 0 0 0 0
	0x06, 0x06, 0x86, 0xe2, 0x78, 0x1e, 0x06, 0x00,
	// 0 0 1 1 0 0 0 0
	// 0 1 1 0 0 0 0 0
	// 0 1 1 0 0 0 0 0
	// 1 1 0 0 1 1 1 0
	// 1 1 0 1 1 1 1 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x18, 0x1e, 0x07, 0x11, 0x18, 0x18, 0x18, 0x00
};
// }}}

static const char glyf_0[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 1 1 0 1 1 0 0 0
	// 0 1 1 1 0 1 1 1 0 0
	// 1 1 1 0 0 0 1 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 0 0 1 1 0 1 1 0
	// 1 1 0 0 1 1 0 1 1 0
	// 1 1 0 1 1 0 0 1 1 0
	0x1f, 0xfc, 0x0e, 0x86, 0xe0, 0x66, 0x0e, 0xfc, 0xf8, 0x00,
	// 1 1 0 1 1 0 0 1 1 0
	// 1 1 0 0 0 0 0 1 1 0
	// 1 1 1 0 0 0 1 1 1 0
	// 0 1 1 1 0 1 1 1 0 0
	// 0 0 1 1 0 1 1 0 0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	0x07, 0x0f, 0x1c, 0x19, 0x01, 0x18, 0x1c, 0x0f, 0x07, 0x00
};
// }}}

static const char glyf_1[] = {
	// {{{
	// 0 0 0 0|0 0
	// 0 1 0 1 1 0
	// 1 1 0 1 1 0
	// 1 1 0 1 1 0
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	0x0c, 0x0e, 0x00, 0xfe, 0xfe, 0x00,
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	0x00, 0x00, 0x00, 0x1f, 0x1f, 0x00
};
// }}}

static const char glyf_2[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 1 1 1 0 1 0 0
	// 1 1 1 1 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 1 1 1 0
	// 0 0 0 1 1 1 0 0
	// 0 0 1 1 1 0 0 0
	0x0c, 0x0e, 0x86, 0xc6, 0xe0, 0x7e, 0x3c, 0x00,
	// 0 1 1 1 0 0 0 0
	// 0 0 1 0 0 0 0 0
	// 1 0 0 0 0 0 0 0
	// 1 1 1 1 1 1 1 0
	// 1 1 1 1 1 1 1 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x1c, 0x19, 0x1b, 0x19, 0x18, 0x18, 0x18, 0x00
};
// }}}

static const char glyf_3[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 1 1 0 1 1 0 0
	// 1 1 1 0 1 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 1 1 1 0
	// 0 0 0 1 1 1 0 0
	// 0 0 0 1 1 1 0 0
	0x0c, 0x0e, 0x06, 0xc0, 0xe6, 0xfe, 0x3c, 0x00,
	// 0 0 0 0 1 1 1 0
	// 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 1 0 1 1 1 0
	// 0 1 1 0 1 1 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x0c, 0x1c, 0x18, 0x00, 0x19, 0x1f, 0x0f, 0x00
};
// }}}

static const char glyf_4[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 1 0 1 1 0
	// 0 0 1 1 0 1 1 0
	// 0 0 1 1 0 1 1 0
	// 0 1 1 0 0 1 1 0
	// 0 1 1 0 0 1 1 0
	0x00, 0xc0,  0xf0, 0x38, 0x00, 0xfe, 0xfe, 0x00,
	// 1 1 0 0 0 1 1 0
	// 1 1 1 1 0 1 1 0
	// 1 1 1 1 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x07, 0x07, 0x06, 0x06, 0x00, 0x1f, 0x1f, 0x00
};
// }}}

static const char glyf_5[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 1 1 1 1 1 1 0 0
	// 1 1 1 1 1 1 0 0
	// 0 0 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 1 1 1 1 0 0
	// 1 1 1 1 1 1 1 0
	// 0 0 0 0 0 1 1 0
	0x76, 0x76, 0x66, 0x66, 0x66, 0xe6, 0xc0, 0x00,
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 1 1 1 1 1 0
	// 0 1 1 1 1 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x0c, 0x1c, 0x18, 0x18, 0x18, 0x0e, 0x0e, 0x00
};
// }}}

static const char glyf_6[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 1 1 0 1 1 0 0
	// 1 1 1 0 1 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 0
	// 1 1 0 0 0 0 0 0
	// 1 1 1 0 1 1 0 0
	// 1 1 1 0 1 1 1 0
	0xfc, 0xfe, 0xc6, 0x00, 0xc6, 0xce, 0x8c, 0x00,
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 1 0 1 1 1 0
	// 0 1 1 0 1 1 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x0f, 0x1f, 0x18, 0x00, 0x18, 0x1f, 0x0f, 0x00
};
// }}}

static const char glyf_7[] = {
	// {{{
	// 0 0 0 0|0 0 0
	// 1 1 1 1 1 1 0
	// 1 1 1 1 1 1 0
	// 0 0 0 0 1 1 0
	// 0 0 0 0 0 0 0
	// 0 0 0 1 1 0 0
	// 0 0 0 1 1 0 0
	// 0 0 1 1 0 0 0
	0x06, 0x06, 0x86, 0xe6, 0x6e, 0x0e, 0x00,
	// 0 0 1 1 0 0 0
	// 0 0 1 1 0 0 0
	// 0 1 1 0 0 0 0
	// 0 1 1 0 0 0 0
	// 0 1 1 0 0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	0x00, 0x1c, 0x1f, 0x03, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_8[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 1 1 0 1 1 0 0
	// 1 1 1 0 1 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 1 1 0 1 1 0 0
	// 0 1 1 0 1 1 0 0
	0x3c, 0xfe, 0x36, 0x00, 0x36, 0xfe, 0x3c, 0x00,
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 1 0 1 1 1 0
	// 0 1 1 0 1 1 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x0f, 0x1f, 0x18, 0x00, 0x18, 0x1f, 0x0f, 0x00
};
// }}}

static const char glyf_9[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 1 1 0 1 1 0 0
	// 1 1 1 0 1 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 1 0 1 1 1 0
	// 0 1 1 0 1 1 1 0
	0x7c, 0xfe, 0xc6, 0x00, 0xc6, 0xfe, 0xfc, 0x00,
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 1 0 1 1 1 0
	// 0 1 1 0 1 1 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x0c, 0x1c, 0x18, 0x00, 0x18, 0x1f, 0x0f, 0x00
};
// }}}

static const char glyf_colon[] = {
	// {{{
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 0 0 0
	0x60, 0x60, 0x00,
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	0x06, 0x06, 0x00
};
// }}}

static const char glyf_semicolon[] = {
	// {{{
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 0 0 0
	0x60, 0x60, 0x00,
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 0 1 0
	// 0 1 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	0x06, 0x1e, 0x00
};
// }}}

static const char glyf_period[] = {
	// {{{
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	0x00, 0x00, 0x00,
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	0x18, 0x18, 0x00
};
// }}}

static const char glyf_comma[] = {
	// {{{
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	0x00, 0x00, 0x00,
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 0 1 0
	// 0 1 0
	// 0 0 0
	0x18, 0x78, 0x00
};
// }}}

static const char glyf_space[] = {
	// {{{
	0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_plus[] = {
	// {{{
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 1 1 0 0 0
	// 0 0 1 1 0 0 0
	// 1 1 1 1 1 1 0
	// 1 1 1 1 1 1 0
	0xc0, 0xc0, 0xf0, 0xf0, 0xc0, 0xc0, 0x00,
	// 0 0 1 1 0 0 0
	// 0 0 1 1 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	0x00, 0x00, 0x03, 0x03, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_minus[] = {
	// {{{
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 1 1 1 1 1 1 0
	// 1 1 1 1 1 1 0
	0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0x00,
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_equals[] = {
	// {{{
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 1 1 1 1 1 1 0
	// 1 1 1 1 1 1 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x00,
	// 1 1 1 1 1 1 0
	// 1 1 1 1 1 1 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x00
};
// }}}

static const char glyf_slash[] = {
	// {{{
	// 0 0 0 0|0 0
	// 0 0 0 1|1 0
	// 0 0 0 1|1 0
	// 0 0 0 1|1 0
	// 0 0 1 1|0 0
	// 0 0 1 1|0 0
	// 0 0 1 1|0 0
	// 0 1 1 0|0 0
	0x00, 0x80, 0xf0, 0x7e, 0x0e, 0x00,
	// 0 1 1 0 0 0
	// 0 1 1 0 0 0
	// 1 1 0 0 0 0
	// 1 1 0 0 0 0
	// 1 1 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	0x1c, 0x1f, 0x03, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_backslash[] = {
	// {{{
	// 0 0 0 0|0 0
	// 1 1 0 0|0 0
	// 1 1 0 0|0 0
	// 1 1 0 0 0 0
	// 0 1 1 0 0 0
	// 0 1 1 0 0 0
	// 0 1 1 0 0 0
	// 0 0 1 1 0 0
	0x0e, 0x7e, 0xf0, 0x80, 0x00, 0x00,
	// 0 0 1 1 0 0
	// 0 0 1 1 0 0
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0
	0x00, 0x00, 0x03, 0x1f, 0x1c, 0x00
};
// }}}

static const char glyf_exclamation[] = {
	// {{{
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	0xfe, 0xfe, 0x00,
	// 1 1 0
	// 0 0 0
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	0x19, 0x19, 0x00
};
// }}}

static const char glyf_left_bracket[] = {
	// {{{
	// 0 0 0 0 0
	// 1 1 1 1 0
	// 1 1 1 1 0
	// 1 1 0 0 0
	// 1 1 0 0 0
	// 1 1 0 0 0
	// 1 1 0 0 0
	// 1 1 0 0 0
	0xfe, 0xfe, 0x06, 0x06, 0x00,
	// 1 1 0 0 0
	// 1 1 0 0 0
	// 1 1 0 0 0
	// 1 1 1 1 0
	// 1 1 1 1 0
	// 0 0 0 0 0
	// 0 0 0 0 0
	// 0 0 0 0 0
	0x1f, 0x1f, 0x18, 0x18, 0x00
};
// }}}

static const char glyf_right_bracket[] = {
	// {{{
	// 0 0 0 0 0
	// 1 1 1 1 0
	// 1 1 1 1 0
	// 0 0 1 1 0
	// 0 0 1 1 0
	// 0 0 1 1 0
	// 0 0 1 1 0
	// 0 0 1 1 0
	0x06, 0x06, 0xfe, 0xfe, 0x00,
	// 0 0 1 1 0
	// 0 0 1 1 0
	// 0 0 1 1 0
	// 1 1 1 1 0
	// 1 1 1 1 0
	// 0 0 0 0 0
	// 0 0 0 0 0
	// 0 0 0 0 0
	0x18, 0x18, 0x1f, 0x1f, 0x00
};
// }}}

static const char glyf_left_paren[] = {
	// {{{
	// 0 0 0 0 0
	// 0 0 1 1 0
	// 0 0 1 1 0
	// 0 1 1 0 0
	// 0 1 1 0 0
	// 0 1 1 0 0
	// 1 1 0 0 0
	// 1 1 0 0 0
	0xc0, 0xf8, 0x3e, 0x06, 0x00,
	// 1 1 0 0 0
	// 0 1 1 0 0
	// 0 1 1 0 0
	// 0 1 1 0 0
	// 0 0 1 1 0
	// 0 0 1 1 0
	// 0 0 0 0 0
	// 0 0 0 0 0
	0x01, 0x0f, 0x3e, 0x30, 0x00
};
// }}}

static const char glyf_right_paren[] = {
	// {{{
	// 0 0 0 0 0 0
	// 1 1 0 0 0 0
	// 1 1 0 0 0 0
	// 0 0 1 1 0 0
	// 0 0 1 1 0 0
	// 0 0 1 1 0 0
	// 0 0 0 1 1 0
	// 0 0 0 1 1 0
	0x06, 0x06, 0x38, 0xf8, 0xc0, 0x00,
	// 0 0 0 1 1 0
	// 0 0 1 1 0 0
	// 0 0 1 1 0 0
	// 0 0 1 1 0 0
	// 0 1 1 0 0 0
	// 0 1 1 0 0 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	0x00, 0x30, 0x3e, 0x0f, 0x01, 0x00
};
// }}}

static const char glyf_underscore[] = {
	// {{{
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 1 1 1 1|1 1 0
	// 1 1 1 1|1 1 0
	// 0 0 0 0|0 0 0
	0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x00
};
// }}}

// GOT THIS FAR

static const char glyf_dollar[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 1 1 0|1 1 0 0
	// 0 1 1 0|1 1 0 0
	// 1 1 1 0|1 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0 0 0 0 0
	// 1 1 1 1 1 1 0 0
	// 0 1 1 1 1 1 1 0
	0x78, 0xfe, 0xce, 0xc0, 0xce, 0xde, 0x98, 0x00,
	// 0 0 0 0 0 1 1 0
	// 1 1 0 0 0 1 1 0
	// 1 1 1 0|1 1 1 0
	// 0 1 1 0|1 1 0 0
	// 0 1 1 0|1 1 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	0x06, 0x1e, 0x1c, 0x00, 0x1c, 0x1f, 0x07, 0x00
};
// }}}

static const char glyf_percent[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0 0 0
	// 0 1 1 1|0 0 0 1|1 0 0 0
	// 1 1 0 1|1 0 0 1|1 0 0 0
	// 1 1 0 1|1 0 1 1|0 0 0 0
	// 0 1 1 1|0 0 1 1 0 0 0 0
	// 0 0 0 0 0 1 1 0 0 0 0 0
	// 0 0 0 0 0 1 1 0 0 0 0 0
	// 0 0 0 0 1 1 0 0 0 0 0 0
	0x0c, 0x1e, 0x12, 0x1e, 0x8c, 0xe0, 0x78, 0x1e, 0x06, 0x00, 0x00, 0x00,
	// 0 0 0 0 1 1 0 0 0 0 0 0
	// 0 0 0 1 1 0 0 1 1 1 0 0
	// 0 0 0 1 1 0 1 1 0 1 1 0
	// 0 0 1 1 0 0 1 1 0 1 1 0
	// 0 0 1 1 0 0 0 1 1 1 0 0
	// 0 0 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0|0 0 0 0 0 0 0 0
	// 0 0 0 0|0 0 0 0 0 0 0 0
	0x00, 0x00, 0x18, 0x1e, 0x07, 0x01, 0x0c, 0x1e, 0x12, 0x1e, 0x0c, 0x00
};
// }}}

static const char glyf_quote[] = {
	// {{{
	// 0 0 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	0x0e, 0x0e, 0x00,
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	0x00, 0x00, 0x00
};
// }}}

static const char glyf_double_quote[] = {
	// {{{
	// 0 0 0 0|0 0
	// 1 1 0 1|1 0
	// 1 1 0 1|1 0
	// 1 1 0 1|1 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	0x0e, 0x0e, 0x00, 0x0e, 0x0e, 0x00,
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_back_quote[] = {
	// {{{
	// 0 0 0 0|
	// 1 1 0 0|
	// 1 1 0 0|
	// 0 1 1 0|
	// 0 1 1 0|
	// 0 0 0 0|
	// 0 0 0 0|
	// 0 0 0 0|
	0x06, 0x1e, 0x18, 0x00,
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	// 0 0 0 0|0 0
	0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_pound[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0
	// 0 1 1 0|0 0 1 1|0 0
	// 0 1 1 0|0 0 1 1|0 0
	// 1 1 1 1|0 1 1 1|1 0
	// 1 1 1 1|0 1 1 1|1 0
	// 0 1 1 0 0 0 1 1 0 0
	// 0 1 1 0 0 0 1 1 0 0
	// 0 1 1 0 0 0 1 1 0 0
	0x18, 0xfe, 0xfe, 0x18, 0x00, 0x18, 0xfe, 0xfe, 0x18, 0x00,
	// 1 1 1 1 0 1 1 1 1 0
	// 1 1 1 1 0 1 1 1 1 0
	// 0 1 1 0|0 0 1 1 0 0
	// 0 1 1 0|0 0 1 1 0 0
	// 0 0 0 0|0 0 0 0 0 0
	// 0 0 0 0|0 0 0 0 0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	0x03, 0x0f, 0x0f, 0x03, 0x00, 0x03, 0x0f, 0x0f, 0x03, 0x00
};
// }}}

static const char glyf_pipe[] = {
	// {{{
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	0xff, 0xff, 0x00,
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 1 1 0
	// 0 0 0
	// 0 0 0
	0x3f, 0x3f, 0x00
};
// }}}

static const char glyf_lt[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 0|0 0 1 1|0
	// 0 0 0 0|1 1 1 1|0
	// 0 0 1 1 1 1 0 0 0
	// 1 1 1 1 0 0 0 0 0
	// 1 1 0 0 0 0 0 0 0
	// 1 1 1 1 0 0 0 0 0
	0xe0, 0xe0, 0xb0, 0xb0, 0x18, 0x18, 0x0c, 0x0c, 0x00,
	// 0 0 1 1 1 1 0 0 0
	// 0 0 0 0|1 1 1 1|0
	// 0 0 0 0|0 0 1 1|0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	0x00, 0x00, 0x01, 0x01, 0x03, 0x03, 0x06, 0x06, 0x00
};
// }}}

static const char glyf_gt[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0
	// 0 0 0 0|0 0 0 0|0
	// 1 1 0 0|0 0 0 0|0
	// 1 1 1 1|0 0 0 0|0
	// 0 0 1 1 1 1 0 0 0
	// 0 0 0 0 1 1 1 1 0
	// 0 0 0 0 0 0 1 1 0
	// 0 0 0 0 1 1 1 1 0
	0x0c, 0x0c, 0x18, 0x18, 0xb0, 0xb0, 0xe0, 0xe0, 0x00,
	// 0 0 1 1 1 1 0 0 0
	// 1 1 1 1 0 0 0 0 0
	// 1 1 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0
	0x06, 0x06, 0x03, 0x03, 0x01, 0x01, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_question[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 1 1 0|1 1 0 0
	// 1 1 1 0|1 1 1 0
	// 1 1 0 0 0 1 1 0
	// 0 0 0 0 0 1 1 0
	// 0 0 0 0|1 1 1 0
	// 0 0 0 1|1 1 0 0
	// 0 0 1 1 1 0 0 0
	0x0c, 0x0e, 0x16, 0xc0, 0xe6, 0x7e, 0x3c, 0x00,
	// 0 0 1 1 0 0 0 0
	// 0 0 1 1|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 1 1 0 0 0 0
	// 0 0 1 1 0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0|0 0 0 0
	// 0 0 0 0 0 0 0 0
	0x00, 0x00, 0x1b, 0x1b, 0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_ampersand[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0 0
	// 0 0 1 1|0 1 1 0|0 0 0
	// 0 0 1 1|0 1 1 0|0 0 0
	// 0 1 1 0 0 0 1 1 0 0 0
	// 0 1 1 1 0 0 1 1 0 0 0
	// 0 0 1 1|0 0 1 0|0 0 0
	// 0 0 0 1|1 0 0 0|0 0 0
	// 0 1 0 1 1 1 0 0 0 0 0
	0x00, 0x18, 0x3e, 0xf6, 0xc0, 0x86, 0x3e, 0x18, 0x00, 0x00, 0x00,
	// 1 1 0 0 1 1 1 0 0 0 0
	// 1 1 0 0|0 1 1 1|0 0 0
	// 1 1 0 0|0 0 1 1|1 0 0
	// 1 1 1 1 1 0 0 1 1 1 0
	// 0 1 1 1 1 1 0 0 1 1 0
	// 0 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0 0 0
	0x0f, 0x1f, 0x18, 0x18, 0x19, 0x1c, 0x07, 0x0e, 0x1c, 0x18, 0x00
};
// }}}

static const char glyf_star[] = {
	// {{{
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0|0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 1 1 0 0 0
	// 0 0 1 1|0 0 0
	// 1 1 1 1|1 1 0
	// 1 1 1 1|1 1 0
	0xc0, 0xc0, 0xf0, 0xf0, 0xc0, 0xc0, 0x00,
	// 0 1 1 1 1 0 0
	// 1 1 1 1|1 1 0
	// 1 1 0 0|1 1 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0
	0x06, 0x07, 0x03, 0x03, 0x07, 0x06, 0x00
};
// }}}

static const char glyf_carat[] = {
	// {{{
	// 0 0 0 0|0 0 0 0
	// 0 0 1 1|1 0 0 0
	// 0 0 1 1|1 0 0 0
	// 0 1 1 0|1 1 0 0
	// 0 1 1 0 1 1 0 0
	// 1 1 0 0 0 1 1 0
	// 1 1 0 0|0 1 1 0
	// 0 0 0 0|0 0 0 0
	0x60, 0x78, 0x1e, 0x06, 0x1e, 0x78, 0x60, 0x00,
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_tilde[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0|0 0 0 0|0 0
	// 0 0 1 1|1 0 0 1|1 0
	// 1 1 1 1 1 1 1 1 1 0
	0x80, 0x80, 0xc0, 0xc0, 0xc0, 0x80, 0x80, 0xc0, 0xc0, 0x00,
	// 1 1 0 0 1 1 1 0 0 0
	// 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0 0
	0x01, 0x01, 0x00, 0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00
};
// }}}

static const char glyf_at[] = {
	// {{{
	// 0 0 0 0|0 0 0 0|0 0 0 0|0 0 0
	// 0 0 0 1|1 1 0 1|1 1 1 0 0 0 0
	// 0 1 1 1 1 1 1 1 1 0 0 1 0 0 0
	// 0 1 1 0 0 0 0 0 0 0 0 0 1 1 0
	//
	// 1 1 0 0 0 1 1 1 1 1 0 0 1 1 0
	// 1 1 0 0|1 1 1 1|1 1 0 0|1 1 0
	// 1 1 0 1|1 1 0 0|1 1 0 0|1 1 0
	// 0 0 0 1 1 0 0 0 1 1 0 0 0 0 0
	0x70, 0x7c, 0x0c, 0x36, 0xe6, 0x76, 0x34, 0x36, 0xf6, 0xf2, 0x02, 0x40, 0x78, 0x78, 0x00,
	// 0 0 0 1 1 0 0 0 1 1 0 0 1 1 0
	// 1 1 0 1|1 0 0 1|1 1 0 0|1 1 0
	// 1 1 0 1|1 1 1 1|1 1 1 1|1 1 0
	// 1 1 0 0 1 1 1 0 1 1 1 1 1 0 0

	// 1 1 1 0 0 0 0 0 0 0 0 0 0 0 0
	// 0 1 1 1 1 1 0 1 1 1 1 0 0 0 0
	// 0 0 0 1 1 1 0 1 1 1 1 0 0 0 0
	// 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
	0x1e, 0x3e, 0x30, 0x67, 0x6f, 0x63, 0x0c, 0x66, 0x6f, 0x6f, 0x63, 0x0c, 0x0f, 0x07, 0x00
};
// }}}

void	init_tall_glyfs(void) {
	tallfontp = &tallfont;
	tallfont.m_fixed  = 0;
	tallfont.m_height = 2;
	for(int i=0; i<128; i++) {
		tallfont.m_ln[i]   = 0;
		tallfont.m_datp[i] = NULL;
	}

	// Capitals
	// {{{
	tallfont.m_datp['A'] = glyf_A; tallfont.m_ln['A'] = sizeof(glyf_A); 
	tallfont.m_datp['B'] = glyf_B; tallfont.m_ln['B'] = sizeof(glyf_B); 
	tallfont.m_datp['C'] = glyf_C; tallfont.m_ln['C'] = sizeof(glyf_C); 
	tallfont.m_datp['D'] = glyf_D; tallfont.m_ln['D'] = sizeof(glyf_D); 
	tallfont.m_datp['E'] = glyf_E; tallfont.m_ln['E'] = sizeof(glyf_E); 
	tallfont.m_datp['F'] = glyf_F; tallfont.m_ln['F'] = sizeof(glyf_F); 
	tallfont.m_datp['G'] = glyf_G; tallfont.m_ln['G'] = sizeof(glyf_G); 
	tallfont.m_datp['H'] = glyf_H; tallfont.m_ln['H'] = sizeof(glyf_H); 
	tallfont.m_datp['I'] = glyf_I; tallfont.m_ln['I'] = sizeof(glyf_I); 
	tallfont.m_datp['J'] = glyf_J; tallfont.m_ln['J'] = sizeof(glyf_J); 
	tallfont.m_datp['K'] = glyf_K; tallfont.m_ln['K'] = sizeof(glyf_K); 
	tallfont.m_datp['L'] = glyf_L; tallfont.m_ln['L'] = sizeof(glyf_L); 
	tallfont.m_datp['M'] = glyf_M; tallfont.m_ln['M'] = sizeof(glyf_M); 
	tallfont.m_datp['N'] = glyf_N; tallfont.m_ln['N'] = sizeof(glyf_N); 
	tallfont.m_datp['O'] = glyf_O; tallfont.m_ln['O'] = sizeof(glyf_O); 
	tallfont.m_datp['P'] = glyf_P; tallfont.m_ln['P'] = sizeof(glyf_P); 
	tallfont.m_datp['Q'] = glyf_Q; tallfont.m_ln['Q'] = sizeof(glyf_Q); 
	tallfont.m_datp['R'] = glyf_R; tallfont.m_ln['R'] = sizeof(glyf_R); 
	tallfont.m_datp['S'] = glyf_S; tallfont.m_ln['S'] = sizeof(glyf_S); 
	tallfont.m_datp['T'] = glyf_T; tallfont.m_ln['T'] = sizeof(glyf_T); 
	tallfont.m_datp['U'] = glyf_U; tallfont.m_ln['U'] = sizeof(glyf_U); 
	tallfont.m_datp['V'] = glyf_V; tallfont.m_ln['V'] = sizeof(glyf_V); 
	tallfont.m_datp['W'] = glyf_W; tallfont.m_ln['W'] = sizeof(glyf_W); 
	tallfont.m_datp['X'] = glyf_X; tallfont.m_ln['X'] = sizeof(glyf_X); 
	tallfont.m_datp['Y'] = glyf_Y; tallfont.m_ln['Y'] = sizeof(glyf_Y); 
	tallfont.m_datp['Z'] = glyf_Z; tallfont.m_ln['Z'] = sizeof(glyf_Z); 
	// }}}

	// Lower case
	// {{{
	for(int s='A', d='a'; s <= 'Z'; s++, d++) {
		tallfont.m_datp[d] = tallfont.m_datp[s];
		tallfont.m_ln[d] = tallfont.m_ln[s];
	}
	/*
	tallfont.m_datp['a'] = glyf_a; tallfont.m_ln['a'] = sizeof(glyf_a); 
	tallfont.m_datp['b'] = glyf_b; tallfont.m_ln['b'] = sizeof(glyf_b); 
	tallfont.m_datp['c'] = glyf_c; tallfont.m_ln['c'] = sizeof(glyf_c); 
	tallfont.m_datp['d'] = glyf_d; tallfont.m_ln['d'] = sizeof(glyf_d); 
	tallfont.m_datp['e'] = glyf_e; tallfont.m_ln['e'] = sizeof(glyf_e); 
	tallfont.m_datp['f'] = glyf_f; tallfont.m_ln['f'] = sizeof(glyf_f); 
	tallfont.m_datp['g'] = glyf_g; tallfont.m_ln['g'] = sizeof(glyf_g); 
	tallfont.m_datp['h'] = glyf_h; tallfont.m_ln['h'] = sizeof(glyf_h); 
	tallfont.m_datp['i'] = glyf_i; tallfont.m_ln['i'] = sizeof(glyf_i); 
	tallfont.m_datp['j'] = glyf_j; tallfont.m_ln['j'] = sizeof(glyf_j); 
	tallfont.m_datp['k'] = glyf_k; tallfont.m_ln['k'] = sizeof(glyf_k); 
	tallfont.m_datp['l'] = glyf_l; tallfont.m_ln['l'] = sizeof(glyf_l); 
	tallfont.m_datp['m'] = glyf_m; tallfont.m_ln['m'] = sizeof(glyf_m); 
	tallfont.m_datp['n'] = glyf_n; tallfont.m_ln['n'] = sizeof(glyf_n); 
	tallfont.m_datp['o'] = glyf_o; tallfont.m_ln['o'] = sizeof(glyf_o); 
	tallfont.m_datp['p'] = glyf_p; tallfont.m_ln['p'] = sizeof(glyf_p); 
	tallfont.m_datp['q'] = glyf_q; tallfont.m_ln['q'] = sizeof(glyf_q); 
	tallfont.m_datp['r'] = glyf_r; tallfont.m_ln['r'] = sizeof(glyf_r); 
	tallfont.m_datp['s'] = glyf_s; tallfont.m_ln['s'] = sizeof(glyf_s); 
	tallfont.m_datp['t'] = glyf_t; tallfont.m_ln['t'] = sizeof(glyf_t); 
	tallfont.m_datp['u'] = glyf_u; tallfont.m_ln['u'] = sizeof(glyf_u); 
	tallfont.m_datp['v'] = glyf_v; tallfont.m_ln['v'] = sizeof(glyf_v); 
	tallfont.m_datp['w'] = glyf_w; tallfont.m_ln['w'] = sizeof(glyf_w); 
	tallfont.m_datp['x'] = glyf_x; tallfont.m_ln['x'] = sizeof(glyf_x); 
	tallfont.m_datp['y'] = glyf_y; tallfont.m_ln['y'] = sizeof(glyf_y); 
	tallfont.m_datp['z'] = glyf_z; tallfont.m_ln['z'] = sizeof(glyf_z); 
	*/
	// }}}

	// Digits
	// {{{
	tallfont.m_datp['0'] = glyf_0; tallfont.m_ln['0'] = sizeof(glyf_0); 
	tallfont.m_datp['1'] = glyf_1; tallfont.m_ln['1'] = sizeof(glyf_1); 
	tallfont.m_datp['2'] = glyf_2; tallfont.m_ln['2'] = sizeof(glyf_2); 
	tallfont.m_datp['3'] = glyf_3; tallfont.m_ln['3'] = sizeof(glyf_3); 
	tallfont.m_datp['4'] = glyf_4; tallfont.m_ln['4'] = sizeof(glyf_4); 
	tallfont.m_datp['5'] = glyf_5; tallfont.m_ln['5'] = sizeof(glyf_5); 
	tallfont.m_datp['6'] = glyf_6; tallfont.m_ln['6'] = sizeof(glyf_6); 
	tallfont.m_datp['7'] = glyf_7; tallfont.m_ln['7'] = sizeof(glyf_7); 
	tallfont.m_datp['8'] = glyf_8; tallfont.m_ln['8'] = sizeof(glyf_8); 
	tallfont.m_datp['9'] = glyf_9; tallfont.m_ln['9'] = sizeof(glyf_9); 
	// }}}

	// Special characters
	// {{{
	tallfont.m_datp[':'] = glyf_colon; tallfont.m_ln[':'] = sizeof(glyf_colon); 
	tallfont.m_datp[';'] = glyf_semicolon; tallfont.m_ln[';'] = sizeof(glyf_semicolon); 
	tallfont.m_datp['.'] = glyf_period; tallfont.m_ln['.'] = sizeof(glyf_period); 
	tallfont.m_datp[','] = glyf_comma; tallfont.m_ln[','] = sizeof(glyf_comma); 
	tallfont.m_datp['?'] = glyf_question; tallfont.m_ln['?'] = sizeof(glyf_question); 
	tallfont.m_datp[' '] = glyf_space; tallfont.m_ln[' '] = sizeof(glyf_space); 
	tallfont.m_datp['@'] = glyf_at; tallfont.m_ln['@'] = sizeof(glyf_at); 
	tallfont.m_datp['#'] = glyf_pound; tallfont.m_ln['#'] = sizeof(glyf_pound); 
	tallfont.m_datp['!'] = glyf_exclamation; tallfont.m_ln['!'] = sizeof(glyf_exclamation); 
	tallfont.m_datp['%'] = glyf_percent; tallfont.m_ln['%'] = sizeof(glyf_percent); 
	tallfont.m_datp['^'] = glyf_carat; tallfont.m_ln['^'] = sizeof(glyf_carat); 
	tallfont.m_datp['&'] = glyf_ampersand; tallfont.m_ln['&'] = sizeof(glyf_ampersand); 
	tallfont.m_datp['*'] = glyf_star; tallfont.m_ln['*'] = sizeof(glyf_star); 
	tallfont.m_datp['('] = glyf_left_paren; tallfont.m_ln['('] = sizeof(glyf_left_paren); 
	tallfont.m_datp[')'] = glyf_right_paren; tallfont.m_ln[')'] = sizeof(glyf_right_paren); 
	tallfont.m_datp['['] = glyf_left_bracket; tallfont.m_ln['['] = sizeof(glyf_left_bracket); 
	tallfont.m_datp[']'] = glyf_right_bracket; tallfont.m_ln[']'] = sizeof(glyf_right_bracket); 
	tallfont.m_datp['/'] = glyf_slash; tallfont.m_ln['/'] = sizeof(glyf_slash); 
	tallfont.m_datp['\\'] = glyf_backslash; tallfont.m_ln['\\'] = sizeof(glyf_backslash); 
	tallfont.m_datp['<'] = glyf_lt; tallfont.m_ln['<'] = sizeof(glyf_lt); 
	tallfont.m_datp['>'] = glyf_gt; tallfont.m_ln['>'] = sizeof(glyf_gt); 
	tallfont.m_datp['\''] = glyf_quote; tallfont.m_ln['\''] = sizeof(glyf_quote); 
	tallfont.m_datp['\"'] = glyf_double_quote; tallfont.m_ln['\"'] = sizeof(glyf_double_quote); 
	tallfont.m_datp['`'] = glyf_back_quote; tallfont.m_ln['`'] = sizeof(glyf_back_quote); 
	tallfont.m_datp['|'] = glyf_pipe; tallfont.m_ln['|'] = sizeof(glyf_pipe); 
	tallfont.m_datp['~'] = glyf_tilde; tallfont.m_ln['~'] = sizeof(glyf_tilde); 
	tallfont.m_datp['$'] = glyf_dollar; tallfont.m_ln['$'] = sizeof(glyf_dollar); 
	tallfont.m_datp['='] = glyf_equals; tallfont.m_ln['='] = sizeof(glyf_equals); 
	tallfont.m_datp['+'] = glyf_plus; tallfont.m_ln['+'] = sizeof(glyf_plus); 
	tallfont.m_datp['-'] = glyf_minus; tallfont.m_ln['-'] = sizeof(glyf_minus); 
	tallfont.m_datp['_'] = glyf_underscore; tallfont.m_ln['_'] = sizeof(glyf_underscore); 
	// }}}
}

void	set_fixed(OLEDFONT *f) {
	// {{{
	if (!f)
		return;

	int	mx = 0;
	for(int k=0; k<256; k++)
		if(f->m_ln[k] > mx)
			mx = f->m_ln[k];
	if (f->m_height > 1)
		mx = mx / f->m_height;
	f->m_fixed = mx;
}
// }}}
