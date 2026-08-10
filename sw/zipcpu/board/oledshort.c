////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/oledshort.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:
//
// Designed based upon the Connection III Font, found at:
//
//	https://www.fontspace.com/connection-333-font-f31976
// by KineticPlasma Fonts
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
#include "oledfont.h"
// }}}

OLEDFONT	shortfont, *shortfontp;

static const char glyf_A[] = {
	// {{{
	// 0 0 1 0 0 -
	// 0 1 1 1 0 -
	// 1 1 0 1 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 1 1 1 1 0
	// 1 0 0 0 1 0
	// - - - - - -
	0x7c, 0x26, 0x23, 0x26, 0x7c, 0x00
};
// }}}

static const char glyf_B[] = {
	// {{{
	// 1 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 1 1 1 0 0
	// - - - - - -
	0x7f, 0x45, 0x45, 0x45, 0x3a, 0x00
};
// }}}

static const char glyf_C[] = {
	// {{{
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - - -
	0x3e, 0x41, 0x41, 0x41, 0x22, 0x00
};
// }}}

static const char glyf_D[] = {
	// {{{
	// 1 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 1 1 1 0 0
	// - - - - - -
	0x7f, 0x41, 0x41, 0x41, 0x3e, 0x00
};
// }}}

static const char glyf_E[] = {
	// {{{
	// 1 1 1 1 1 0
	// 1 0 0 0 0 0
	// 1 1 1 1 0 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// 1 1 1 1 1 0
	// - - - - - -
	0x7f, 0x45, 0x45, 0x45, 0x41, 0x00
};
// }}}

static const char glyf_F[] = {
	// {{{
	// 1 1 1 1 1 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// 1 1 1 1 0 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// - - - - - -
	0x7f, 0x11, 0x11, 0x11, 0x01, 0x00
};
// }}}

static const char glyf_G[] = {
	// {{{
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 0 0
	// 1 0 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - - -
	0x3e, 0x41, 0x49, 0x49, 0x32, 0x00
};
// }}}

static const char glyf_H[] = {
	// {{{
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 1 1 1 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// - - - - - -
	0x7f, 0x04, 0x04, 0x04, 0x7f, 0x00
};
// }}}

static const char glyf_I[] = {
	// {{{
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// - -
	0x7f, 0x00
};
// }}}

static const char glyf_J[] = {
	// {{{
	// 0 0 1 0
	// 0 0 1 0
	// 0 0 1 0
	// 0 0 1 0
	// 0 0 1 0
	// 0 0 1 0
	// 1 1 0 0
	// - -
	0x40, 0x40, 0x3f, 0x00
};
// }}}

static const char glyf_K[] = {
	// {{{
	// 1 0 0 1 1 0
	// 1 0 0 1 0 0
	// 1 0 1 0 0 0
	// 1 1 0 0 0 0
	// 1 0 1 0 0 0
	// 1 0 0 1 0 0
	// 1 0 0 1 1 0
	// - - - - - -
	0x7f, 0x08, 0x14, 0x63, 0x41, 0x00
};
// }}}

static const char glyf_L[] = {
	// {{{
	// 1 0 0 0 0
	// 1 0 0 0 0
	// 1 0 0 0 0
	// 1 0 0 0 0
	// 1 0 0 0 0
	// 1 0 0 0 0
	// 1 1 1 1 0
	// - - - - - -
	0x7f, 0x40, 0x40, 0x40, 0x00
};
// }}}

static const char glyf_M[] = {
	// {{{
	// 0 1 0 0 0 1 0 0
	// 1 1 1 0 1 1 1 0
	// 1 0 1 0 1 0 1 0
	// 1 0 1 0 1 0 1 0
	// 1 0 1 1 1 0 1 0
	// 1 0 0 1 0 0 1 0
	// 1 0 0 0 0 0 1 0
	// - - - - - - - -
	0x7e, 0x03, 0x1e, 0x30, 0x1e, 0x03, 0x7e, 0x00
};
// }}}

static const char glyf_N[] = {
	// {{{
	// 1 0 0 0 1 0
	// 1 1 0 0 1 0
	// 1 1 0 0 1 0
	// 1 0 1 0 1 0
	// 1 0 0 1 1 0
	// 1 0 0 1 1 0
	// 1 0 0 0 1 0
	// - - - - - - - -
	0x7f, 0x06, 0x08, 0x30, 0x7f, 0x00
};
// }}}

static const char glyf_O[] = {
	// {{{
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - - -
	0x3e, 0x41, 0x41, 0x41, 0x3e, 0x00
};
// }}}

static const char glyf_P[] = {
	// {{{
	// 1 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 1 1 1 0 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// 1 0 0 0 0 0
	// - - - - - -
	0x7f, 0x05, 0x05, 0x05, 0x02, 0x00
};
// }}}

static const char glyf_Q[] = {
	// {{{
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - 1 -
	0x3e, 0x41, 0x41, 0x41, 0xbe, 0x00
};
// }}}

static const char glyf_R[] = {
	// {{{
	// 1 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 1 1 1 1 0
	// 1 0 0 1 0 0
	// 1 0 0 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// - - - - - -
	0x7f, 0x05, 0x05, 0x1d, 0x66, 0x00
};
// }}}

static const char glyf_S[] = {
	// {{{
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 0 0
	// 0 1 1 1 0 0
	// 0 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - - -
	0x26, 0x49, 0x49, 0x49, 0x32, 0x00
};
// }}}

static const char glyf_T[] = {
	// {{{
	// 1 1 1 1 1 0
	// 0 0 1 0 0 0
	// 0 0 1 0 0 0
	// 0 0 1 0 0 0
	// 0 0 1 0 0 0
	// 0 0 1 0 0 0
	// 0 0 1 0 0 0
	// - - - - - -
	0x01, 0x01, 0x7f, 0x01, 0x01, 0x00
};
// }}}

static const char glyf_U[] = {
	// {{{
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - - -
	0x3f, 0x40, 0x40, 0x40, 0x3f, 0x00
};
// }}}

static const char glyf_V[] = {
	// {{{
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 0 1 0 0
	// 0 1 0 1 0 0
	// 0 0 1 0 0 0
	// 0 0 1 0 0 0
	// - - - - - -
	0x07, 0x18, 0x60, 0x18, 0x07, 0x00
};
// }}}

static const char glyf_W[] = {
	// {{{
	// 1 0 0 0 1 0 0 0 1 0
	// 1 0 0 0 1 0 0 0 1 0
	// 1 0 0 0 1 0 0 0 1 0
	// 0 1 0 1 0 1 0 1 0 0
	// 0 1 0 1 0 1 0 1 0 0
	// 0 0 1 0 0 0 1 0 0 0
	// 0 0 1 0 0 0 1 0 0 0
	// - - - - - -
	0x07, 0x18, 0x60, 0x18, 0x07, 0x18, 0x60, 0x18, 0x07, 0x00
};
// }}}

static const char glyf_X[] = {
	// {{{
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 0 1 0 0
	// 0 0 1 0 0 0
	// 0 1 0 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// - - - - - -
	0x63, 0x14, 0x08, 0x14, 0x63, 0x00
};
// }}}

static const char glyf_Y[] = {
	// {{{
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 0 1 0 0
	// 0 1 1 1 0 0
	// 0 0 1 0 0 0
	// 0 0 1 0 0 0
	// 0 0 1 0 0 0
	// - - - - - -
	0x03, 0x0c, 0x78, 0x0c, 0x03, 0x00
};
// }}}

static const char glyf_Z[] = {
	// {{{
	// 1 1 1 1 1 0
	// 0 0 0 0 1 0
	// 0 0 0 1 0 0
	// 0 0 1 0 0 0
	// 0 1 0 0 0 0
	// 1 0 0 0 0 0
	// 1 1 1 1 1 0
	// - - - - - -
	0x61, 0x51, 0x49, 0x45, 0x43, 0x00
};
// }}}

static const char glyf_a[] = {
	// {{{
	// - - - - - -
	// - - - - - -
	// 0 1 1 0 0 0
	// 1 0 0 1 1 0
	// 1 0 0 0 1 0
	// 1 0 0 1 1 0
	// 0 1 1 0 1 0
	// - - - - - -
	0x38, 0x44, 0x44, 0x28, 0x78, 0x00
};
// }}}

static const char glyf_b[] = {
	// {{{
	// 1 0 - - - -
	// 1 0 - - - -
	// 1 0 1 1 0 0
	// 1 1 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - - -
	0x3f, 0x48, 0x44, 0x44, 0x38, 0x00
};
// }}}

static const char glyf_c[] = {
	// {{{
	// 0 0 - - - -
	// 0 0 - - - -
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 0 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - - -
	0x038, 0x44, 0x44, 0x44, 0x28, 0x00
};
// }}}

static const char glyf_d[] = {
	// {{{
	// 0 0 - - 1 -
	// 0 0 - - 1 -
	// 0 1 1 0 1 0
	// 1 0 0 1 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - - -
	0x038, 0x44, 0x44, 0x48, 0x3f, 0x00
};
// }}}

static const char glyf_e[] = {
	// {{{
	// 0 0 - - - -
	// 0 0 - - - -
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 1 1 1 0 0
	// 1 0 0 0 0 0
	// 0 1 1 1 1 0
	// - - - - - -
	0x38, 0x54, 0x54, 0x54, 0x48, 0x00
};
// }}}

static const char glyf_f[] = {
	// {{{
	// 0 0 1 1 -
	// 0 1 - - -
	// 0 1 0 0 0
	// 1 1 1 1 0
	// 0 1 0 0 0
	// 0 1 0 0 0
	// 0 1 0 0 0
	// - - - - - -
	0x008, 0x7e, 0x09, 0x09, 0x00
};
// }}}

static const char glyf_g[] = {
	// {{{
	// - - - - - 0
	// - - - - - 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 0 1 1 1 1 0
	// 0 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	0x48, 0x94, 0x94, 0x94, 0x78, 0x00
};
// }}}

static const char glyf_h[] = {
	// {{{
	// 1 - - - - -
	// 1 - - - - -
	// 1 0 1 1 0 0
	// 1 1 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// - - - - - -
	0x7f, 0x08, 0x04, 0x04, 0x78, 0x00
};
// }}}

static const char glyf_i[] = {
	// {{{
	// 1 0
	// 0 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// - - - - - -
	0x7d, 0x00
};
// }}}

static const char glyf_j[] = {
	// {{{
	// 0 1 0
	// 0 0 0
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// 1 1 0 - - -
	0x80, 0xfd, 0x00
};
// }}}

static const char glyf_k[] = {
	// {{{
	// 1 0 0 0 0
	// 1 0 0 0 0
	// 1 0 0 1 0
	// 1 0 1 0 0
	// 1 1 0 0 0
	// 1 0 1 0 0
	// 1 0 0 1 0
	// - - - - -
	0x7f, 0x10, 0x28, 0x44, 0x00
};
// }}}

static const char glyf_l[] = {
	// {{{
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// - - - - -
	0x7f, 0x00
};
// }}}

static const char glyf_m[] = {
	// {{{
	// - - - - - - - - -
	// - - - - - - - - -
	// 1 0 1 1 0 1 1 0 0
	// 1 1 0 0 1 0 0 1 0
	// 1 0 0 0 1 0 0 1 0
	// 1 0 0 0 1 0 0 1 0
	// 1 0 0 0 1 0 0 1 0
	// - - - - - - - - -
	0x7c, 0x08, 0x04, 0x04, 0x78, 0x04, 0x04, 0x78, 0x00
};
// }}}

static const char glyf_n[] = {
	// {{{
	// - - - - - -
	// - - - - - -
	// 1 0 1 1 0 0
	// 1 1 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// - - - - - -
	0x7c, 0x08, 0x04, 0x04, 0x78, 0x00
};
// }}}

static const char glyf_o[] = {
	// {{{
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 1 1 0 0
	// - - - - -
	0x38, 0x44, 0x44, 0x44, 0x38, 0x00
};
// }}}

static const char glyf_p[] = {
	// {{{
	// - - - - - -
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 1 0 0 1 0
	// 1 0 1 1 0 0
	// 1 - - - - -
	// 1 - - - - -
	0xfc, 0x12, 0x22, 0x22, 0x1c, 0x00
};
// }}}

static const char glyf_q[] = {
	// {{{
	// - - - - - -
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 1 1 0
	// 0 1 1 0 1 0
	// - - - - 1 0
	// - - - - 1 0
	0x1c, 0x22, 0x22, 0x12, 0xfc, 0x00
};
// }}}

static const char glyf_r[] = {
	// {{{
	// - - - - -
	// - - - - -
	// 1 0 1 1 0
	// 1 1 0 0 0
	// 1 0 0 0 0
	// 1 0 0 0 0
	// 1 0 0 0 0
	// - - - - -
	0x7c, 0x08, 0x04, 0x04, 0x00
};
// }}}

static const char glyf_s[] = {
	// {{{
	// 0 0 0 0 0
	// 0 0 0 0 0
	// 0 1 1 1 1
	// 1 0 0 0 0
	// 0 1 1 1 0
	// 0 0 0 0 1
	// 1 1 1 1 0
	// - - - - -
	0x048, 0x54, 0x54, 0x54, 0x24, 0x00
};
// }}}

static const char glyf_t[] = {
	// {{{
	// 0 1 0 0 -
	// 1 1 1 0 -
	// 0 1 0 0 -
	// 0 1 0 0 -
	// 0 1 0 0 -
	// 0 1 0 0 -
	// 0 1 0 0 -
	// - - - - -
	0x02, 0x7f, 0x02, 0x00
};
// }}}

static const char glyf_u[] = {
	// {{{
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 1 1 0
	// 0 1 1 0 1 0
	// - - - - - -
	0x3c, 0x40, 0x40, 0x20, 0x7c, 0x00
};
// }}}

static const char glyf_v[] = {
	// {{{
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 0 1 0 1 0 0
	// 0 1 0 1 0 0
	// 0 0 1 0 0 0
	// - - - - - -
	0x0c, 0x30, 0x40, 0x30, 0x0c, 0x00
};
// }}}

static const char glyf_w[] = {
	// {{{
	// 0 0 0 0 0 0 0 0 0 0
	// 0 0 0 0 0 0 0 0 0 0
	// 1 0 0 0 1 0 0 0 1 0
	// 1 0 0 0 1 0 0 0 1 0
	// 0 1 0 1 0 1 0 1 0 0
	// 0 1 0 1 0 1 0 1 0 0
	// 0 0 1 0 0 0 1 0 0 0
	// - - - - - -
	0x0c, 0x30, 0x40, 0x30, 0x0c, 0x30, 0x40, 0x30, 0x0c, 0x00
};
// }}}

static const char glyf_x[] = {
	// {{{
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 1 0 0 0 1 0
	// 0 1 0 1 0 0

	// 0 0 1 0 0 0
	// 0 1 0 1 0 0
	// 1 0 0 0 1 0
	// - - - - - -
	0x44, 0x28, 0x10, 0x28, 0x44, 0x00
};
// }}}

static const char glyf_y[] = {
	// {{{
	// - - - - - -
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 0 1 0
	// 1 0 0 1 1 0
	// 0 1 1 0 1 0
	// - - - - 1 0
	// - - 1 1 0 0
	0x1e, 0x20, 0xa0, 0x90, 0x7e, 0x00
};
// }}}

static const char glyf_z[] = {
	// {{{
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 1 1 1 1 1 0
	// 0 0 0 1 0 0
	// 0 0 1 0 0 0
	// 0 1 0 0 0 0
	// 1 1 1 1 1 0
	// - - - - - -
	0x44, 0x64, 0x54, 0x4c, 0x44, 0x00
};
// }}}

static const char glyf_0[] = {
	// {{{
	// 0 1 1 0 0
	// 1 0 0 1 0
	// 1 0 0 1 0
	// 1 0 0 1 0
	// 1 0 0 1 0
	// 1 0 0 1 0
	// 0 1 1 0 0
	// - - - - - -
	0x3e, 0x41, 0x41, 0x3e, 0x00
};
// }}}

static const char glyf_1[] = {
	// {{{
	// 0 1 0
	// 1 1 0
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// - - - - - -
	0x02, 0x7f, 0x0
};
// }}}

static const char glyf_2[] = {
	// {{{
	// 0 1 1 0 0
	// 1 0 0 1 0
	// 0 0 0 1 0
	// 0 0 0 1 0
	// 0 1 1 0 0
	// 1 0 0 0 0
	// 1 1 1 1 0
	// - - - - - -
	0x062, 0x51, 0x51, 0x4e, 0x00
};
// }}}

static const char glyf_3[] = {
	// {{{
	// 0 1 1 0 0
	// 1 0 0 1 0
	// 0 0 0 1 0
	// 0 1 1 0 0
	// 0 0 0 1 0
	// 1 0 0 1 0
	// 0 1 1 0 0
	// - - - - - -
	0x022, 0x49, 0x49, 0x36, 0x00
};
// }}}

static const char glyf_4[] = {
	// {{{
	// 0 0 1 1 0 0
	// 0 1 0 1 0 0
	// 1 0 0 1 0 0
	// 1 1 1 1 1 0

	// 0 0 0 1 0 0
	// 0 0 0 1 0 0
	// 0 0 0 1 0 0
	// - - - - - -
	0x0c, 0x0a, 0x09, 0x7f, 0x08, 0x00
};
// }}}

static const char glyf_5[] = {
	// {{{
	// 1 1 1 1 0
	// 1 0 0 0 0
	// 0 1 1 0 0
	// 0 0 0 1 0

	// 0 0 0 1 0
	// 1 0 0 1 0
	// 0 1 1 0 0
	// - - - - - -
	0x23, 0x45, 0x45, 0x39, 0x00
};
// }}}

static const char glyf_6[] = {
	// {{{
	// 0 1 1 0 0
	// 1 0 0 1 0
	// 1 0 0 0 0
	// 1 1 1 0 0
	// 1 0 0 1 0
	// 1 0 0 1 0
	// 0 1 1 0 0
	// - - - - - -
	0x3e, 0x49, 0x49, 0x32, 0x00
};
// }}}

static const char glyf_7[] = {
	// {{{
	// 1 1 1 1 0
	// 0 0 0 1 0
	// 0 0 0 1 0
	// 0 0 1 0 0
	// 0 1 0 0 0
	// 0 1 0 0 0
	// 0 1 0 0 0
	// - - - - - -
	0x1, 0x71, 0x09, 0x07, 0x00
};
// }}}

static const char glyf_8[] = {
	// {{{
	// 0 1 1 0 0
	// 1 0 0 1 0
	// 1 0 0 1 0
	// 0 1 1 0 0
	// 1 0 0 1 0
	// 1 0 0 1 0
	// 0 1 1 0 0
	// - - - - - -
	0x36, 0x49, 0x49, 0x36, 0x00
};
// }}}

static const char glyf_9[] = {
	// {{{
	// 0 1 1 0 0
	// 1 0 0 1 0
	// 1 0 0 1 0
	// 0 1 1 1 0
	// 0 0 0 1 0
	// 1 0 0 1 0
	// 0 1 1 0 0
	// - - - - - -
	0x26, 0x49, 0x49, 0x3e, 0x00
};
// }}}

static const char glyf_colon[] = {
	// {{{
	// 0 0
	// 0 0
	// 1 0
	// 0 0
	// 0 0
	// 0 0
	// 1 0
	// - - - - - -
	0x44, 0x00
};
// }}}

static const char glyf_semicolon[] = {
	// {{{
	// 0 0 0
	// 0 0 0
	// 1 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 1 1 0
	// 1 - - - - -
	0xc4, 0x40, 0x00
};
// }}}

static const char glyf_period[] = {
	// {{{
	// 0 0
	// 0 0
	// 0 0
	// 0 0
	// 0 0
	// 0 0
	// 1 0
	// - - - - - -
	0x40, 0x00
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
	// 1 1 0
	// 1 - - - - -
	0xc0, 0x40, 0x00
};
// }}}

static const char glyf_question[] = {
	// {{{
	// 0 1 1 1 0 0
	// 1 0 0 0 1 0
	// 0 0 0 0 1 0
	// 0 0 0 1 0 0
	// 0 0 1 0 0 0
	// 0 0 0 0 0 0
	// 0 0 1 0 0 0
	// - - - - - -
	0x02, 0x01, 0x51, 0x09, 0x06, 0x00
};
// }}}

static const char glyf_space[] = {
	// {{{
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// - - - - - -
	0x00, 0x00, 0x00
};
// }}}

static const char glyf_at[] = {
	// {{{
	// 0 1 1 1 1 1 0
	// 1 0 0 0 0 0 1
	// 1 0 0 1 1 0 1
	// 1 0 1 0 1 0 1
	// 1 0 0 1 1 1 1
	// 1 0 0 0 0 0 0
	// 0 1 1 1 1 1 0
	// - - - - - - -
	0x3e, 0x41, 0x49, 0x55, 0x5d, 0x51, 0x1e, 0x00
};
// }}}

static const char glyf_pound[] = {
	// {{{
	// 0 1 0 1 0 0
	// 0 1 0 1 0 0
	// 1 1 1 1 1 0
	// 0 1 0 1 0 0
	// 1 1 1 1 1 0
	// 0 1 0 1 0 0
	// 0 1 0 1 0 0
	// - - - - - - -
	0x00, 0x00, 0x00
};
// }}}

static const char glyf_exclamation[] = {
	// {{{
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 0 0
	// 1 0
	// - - - - - - -
	0x5f, 0x00
};
// }}}

static const char glyf_percent[] = {
	// {{{
	// 0 1 1 0 0 0 0 1 0 0
	// 1 0 0 1 0 0 1 0 0 0
	// 1 0 0 1 0 1 0 0 0 0
	// 0 1 1 0 1 0 1 1 0 0
	// 0 0 0 1 0 1 0 0 1 0
	// 0 0 1 0 0 1 0 0 1 0
	// 0 1 0 0 0 0 1 1 0 0
	// - - - - - - -
	0x06, 0x49, 0x29, 0x16, 0x08, 0x34, 0x4a, 0x49, 0x30, 0x00
};
// }}}

static const char glyf_carat[] = {
	// {{{
	// 0 0 1 0 0 0
	// 0 1 0 1 0 0
	// 1 0 0 0 1 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// - - - - - - -
	0x04, 0x02, 0x01, 0x02, 0x04, 0x00
};
// }}}

static const char glyf_ampersand[] = {
	// {{{
	// 0 1 1 1 0 0 0
	// 1 0 0 0 1 0 0
	// 1 0 0 0 0 0 0
	// 0 1 0 0 0 0 0
	// 1 0 0 0 1 1 0
	// 1 0 0 0 1 0 0
	// 0 1 1 1 0 0 0
	// - - - - - - -
	0x036, 0x49, 0x41, 0x41, 0x32, 0x10, 0x00
};
// }}}

static const char glyf_star[] = {
	// {{{
	// - - - -
	// - - - -
	// 1 0 1 0
	// 0 1 0 0
	// 1 0 1 0
	// 0 0 0 0
	// 0 0 0 0
	// - - - - - - -
	0x014, 0x08, 0x14, 0x00
};
// }}}

static const char glyf_left_paren[] = {
	// {{{
	// - 1 - -
	// 1 - - -
	// 1 0 0 0
	// 1 0 0 0
	// 1 0 0 0
	// 1 0 0 0
	// 0 1 0 0
	// - - - - - - -
	0x03e, 0x41, 0x00
};
// }}}

static const char glyf_right_paren[] = {
	// {{{
	// 1 - -
	// 0 1 -
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// 1 0 0
	// - - - - - - -
	0x41, 0x03e, 0x00
};
// }}}

static const char glyf_left_bracket[] = {
	// {{{
	// 1 1 - -
	// 1 - - -
	// 1 0 0 0
	// 1 0 0 0
	// 1 0 0 0
	// 1 0 0 0
	// 1 1 0 0
	// - - - - - - -
	0x07f, 0x41, 0x00
};
// }}}

static const char glyf_right_bracket[] = {
	// {{{
	// 1 1 -
	// 0 1 -
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// 0 1 0
	// 1 1 0
	// - - - - - - -
	0x41, 0x07f, 0x00
};
// }}}

static const char glyf_slash[] = {
	// {{{
	// 0 0 0 0 0 0 1 0
	// 0 0 0 0 0 1 0 0
	// 0 0 0 0 1 0 0 0
	// 0 0 0 1 0 0 0 0
	// 0 0 1 0 0 0 0 0
	// 0 1 0 0 0 0 0 0
	// 1 0 0 0 0 0 0 0
	// - - - - - - -
	0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01, 0x00
};
// }}}

static const char glyf_backslash[] = {
	// {{{
	// 1 0 0 0 0 0 0 0
	// 0 1 0 0 0 0 0 0
	// 0 0 1 0 0 0 0 0
	// 0 0 0 1 0 0 0 0
	// 0 0 0 0 1 0 0 0
	// 0 0 0 0 0 1 0 0
	// 0 0 0 0 0 0 1 0
	// - - - - - - -
	0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x00
};
// }}}

static const char glyf_lt[] = {
	// {{{
	// - - - -
	// 0 0 1 0
	// 0 1 0 0
	// 1 0 0 0
	// 0 1 0 0
	// 0 0 1 0
	// 0 0 0 0
	// - - - - -
	0x08, 0x14, 0x22, 0x00
};
// }}}

static const char glyf_gt[] = {
	// {{{
	// - - - -
	// 1 0 0 0
	// 0 1 0 0
	// 0 0 1 0
	// 0 1 0 0
	// 1 0 0 0
	// 0 0 0 0
	// - - -
	0x22, 0x14, 0x08, 0x00
};
// }}}

static const char glyf_quote[] = {
	// {{{
	// - - -
	// 0 1 0
	// 1 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// - - -
	0x04, 0x02, 0x00
};
// }}}

static const char glyf_double_quote[] = {
	// {{{
	// - - -
	// 0 1 0 1 0
	// 1 0 1 0 0
	// 0 0 0 0 0
	// 0 0 0 0 0
	// 0 0 0 0 0
	// 0 0 0 0 0
	// - - -
	0x04, 0x02, 0x04, 0x02, 0x00
};
// }}}

static const char glyf_back_quote[] = {
	// {{{
	// - - -
	// 1 0 0
	// 0 1 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// - - -
	0x02, 0x04, 0x00
};
// }}}

static const char glyf_pipe[] = {
	// {{{
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// 1 0
	// - - - - -
	0x7f, 0x00
};
// }}}

static const char glyf_tilde[] = {
	// {{{
	// - - -
	// 1 1 0 0
	// 0 0 1 1 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// 0 0 0
	// - - -
	0x02, 0x02, 0x04, 0x04, 0x00
};
// }}}

static const char glyf_dollar[] = {
	// {{{
	// 0 1 1 1 0 0
	// 1 0 1 0 1 0
	// 1 0 1 0 0 0
	// 0 1 1 1 0 0
	// 0 0 1 0 1 0
	// 1 0 1 0 1 0
	// 0 1 1 1 0 0
	// - - - - - -
	0x26, 0x49, 0x7f, 0x49, 0x32, 0x00
};
// }}}

static const char glyf_equals[] = {
	// {{{
	// - - - - -
	// - - - - -
	// 1 1 1 1 0
	// 0 0 0 0 0
	// 1 1 1 1 0
	// 0 0 0 0 0
	// 0 0 0 0 0
	// - - - - - -
	0x14, 0x14, 0x14, 0x14, 0x00
};
// }}}

static const char glyf_plus[] = {
	// {{{
	// - - - 0 0 -
	// - - 1 0 0 -
	// 0 0 1 0 0 0
	// 1 1 1 1 1 0
	// 0 0 1 0 0 0
	// 0 0 1 0 0 0
	// 0 0 0 0 0 0
	// - - - - - -
	0x08, 0x08, 0x3e, 0x08, 0x08, 0x00
};
// }}}

static const char glyf_minus[] = {
	// {{{
	// - - - 0 0 -
	// - - 0 0 0 -
	// 0 0 0 0 0 0
	// 1 1 1 1 1 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// - - - - - -
	0x08, 0x08, 0x08, 0x08, 0x08, 0x00
};
// }}}

static const char glyf_underscore[] = {
	// {{{
	// - - - - - -
	// - - - - - -
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 0 0 0 0 0 0
	// 1 1 1 1 1 0
	0x80, 0x80, 0x80, 0x80, 0x80, 0x00
};
// }}}

void	init_short_glyfs(void) {
	shortfontp = &shortfont;
	shortfont.m_fixed  = 0;
	shortfont.m_height = 1;
	for(int i=0; i<128; i++) {
		shortfont.m_ln[i]   = 0;
		shortfont.m_datp[i] = NULL;
	}

	// Upper case
	// {{{
	shortfont.m_datp['A'] = glyf_A; shortfont.m_ln['A'] = sizeof(glyf_A); 
	shortfont.m_datp['B'] = glyf_B; shortfont.m_ln['B'] = sizeof(glyf_B); 
	shortfont.m_datp['C'] = glyf_C; shortfont.m_ln['C'] = sizeof(glyf_C); 
	shortfont.m_datp['D'] = glyf_D; shortfont.m_ln['D'] = sizeof(glyf_D); 
	shortfont.m_datp['E'] = glyf_E; shortfont.m_ln['E'] = sizeof(glyf_E); 
	shortfont.m_datp['F'] = glyf_F; shortfont.m_ln['F'] = sizeof(glyf_F); 
	shortfont.m_datp['G'] = glyf_G; shortfont.m_ln['G'] = sizeof(glyf_G); 
	shortfont.m_datp['H'] = glyf_H; shortfont.m_ln['H'] = sizeof(glyf_H); 
	shortfont.m_datp['I'] = glyf_I; shortfont.m_ln['I'] = sizeof(glyf_I); 
	shortfont.m_datp['J'] = glyf_J; shortfont.m_ln['J'] = sizeof(glyf_J); 
	shortfont.m_datp['K'] = glyf_K; shortfont.m_ln['K'] = sizeof(glyf_K); 
	shortfont.m_datp['L'] = glyf_L; shortfont.m_ln['L'] = sizeof(glyf_L); 
	shortfont.m_datp['M'] = glyf_M; shortfont.m_ln['M'] = sizeof(glyf_M); 
	shortfont.m_datp['N'] = glyf_N; shortfont.m_ln['N'] = sizeof(glyf_N); 
	shortfont.m_datp['O'] = glyf_O; shortfont.m_ln['O'] = sizeof(glyf_O); 
	shortfont.m_datp['P'] = glyf_P; shortfont.m_ln['P'] = sizeof(glyf_P); 
	shortfont.m_datp['Q'] = glyf_Q; shortfont.m_ln['Q'] = sizeof(glyf_Q); 
	shortfont.m_datp['R'] = glyf_R; shortfont.m_ln['R'] = sizeof(glyf_R); 
	shortfont.m_datp['S'] = glyf_S; shortfont.m_ln['S'] = sizeof(glyf_S); 
	shortfont.m_datp['T'] = glyf_T; shortfont.m_ln['T'] = sizeof(glyf_T); 
	shortfont.m_datp['U'] = glyf_U; shortfont.m_ln['U'] = sizeof(glyf_U); 
	shortfont.m_datp['V'] = glyf_V; shortfont.m_ln['V'] = sizeof(glyf_V); 
	shortfont.m_datp['W'] = glyf_W; shortfont.m_ln['W'] = sizeof(glyf_W); 
	shortfont.m_datp['X'] = glyf_X; shortfont.m_ln['X'] = sizeof(glyf_X); 
	shortfont.m_datp['Y'] = glyf_Y; shortfont.m_ln['Y'] = sizeof(glyf_Y); 
	shortfont.m_datp['Z'] = glyf_Z; shortfont.m_ln['Z'] = sizeof(glyf_Z); 
	// }}}

	// Lower case
	// {{{
	shortfont.m_datp['a'] = glyf_a; shortfont.m_ln['a'] = sizeof(glyf_a); 
	shortfont.m_datp['b'] = glyf_b; shortfont.m_ln['b'] = sizeof(glyf_b); 
	shortfont.m_datp['c'] = glyf_c; shortfont.m_ln['c'] = sizeof(glyf_c); 
	shortfont.m_datp['d'] = glyf_d; shortfont.m_ln['d'] = sizeof(glyf_d); 
	shortfont.m_datp['e'] = glyf_e; shortfont.m_ln['e'] = sizeof(glyf_e); 
	shortfont.m_datp['f'] = glyf_f; shortfont.m_ln['f'] = sizeof(glyf_f); 
	shortfont.m_datp['g'] = glyf_g; shortfont.m_ln['g'] = sizeof(glyf_g); 
	shortfont.m_datp['h'] = glyf_h; shortfont.m_ln['h'] = sizeof(glyf_h); 
	shortfont.m_datp['i'] = glyf_i; shortfont.m_ln['i'] = sizeof(glyf_i); 
	shortfont.m_datp['j'] = glyf_j; shortfont.m_ln['j'] = sizeof(glyf_j); 
	shortfont.m_datp['k'] = glyf_k; shortfont.m_ln['k'] = sizeof(glyf_k); 
	shortfont.m_datp['l'] = glyf_l; shortfont.m_ln['l'] = sizeof(glyf_l); 
	shortfont.m_datp['m'] = glyf_m; shortfont.m_ln['m'] = sizeof(glyf_m); 
	shortfont.m_datp['n'] = glyf_n; shortfont.m_ln['n'] = sizeof(glyf_n); 
	shortfont.m_datp['o'] = glyf_o; shortfont.m_ln['o'] = sizeof(glyf_o); 
	shortfont.m_datp['p'] = glyf_p; shortfont.m_ln['p'] = sizeof(glyf_p); 
	shortfont.m_datp['q'] = glyf_q; shortfont.m_ln['q'] = sizeof(glyf_q); 
	shortfont.m_datp['r'] = glyf_r; shortfont.m_ln['r'] = sizeof(glyf_r); 
	shortfont.m_datp['s'] = glyf_s; shortfont.m_ln['s'] = sizeof(glyf_s); 
	shortfont.m_datp['t'] = glyf_t; shortfont.m_ln['t'] = sizeof(glyf_t); 
	shortfont.m_datp['u'] = glyf_u; shortfont.m_ln['u'] = sizeof(glyf_u); 
	shortfont.m_datp['v'] = glyf_v; shortfont.m_ln['v'] = sizeof(glyf_v); 
	shortfont.m_datp['w'] = glyf_w; shortfont.m_ln['w'] = sizeof(glyf_w); 
	shortfont.m_datp['x'] = glyf_x; shortfont.m_ln['x'] = sizeof(glyf_x); 
	shortfont.m_datp['y'] = glyf_y; shortfont.m_ln['y'] = sizeof(glyf_y); 
	shortfont.m_datp['z'] = glyf_z; shortfont.m_ln['z'] = sizeof(glyf_z); 
	// }}}

	// Digits
	// {{{
	shortfont.m_datp['0'] = glyf_0; shortfont.m_ln['0'] = sizeof(glyf_0); 
	shortfont.m_datp['1'] = glyf_1; shortfont.m_ln['1'] = sizeof(glyf_1); 
	shortfont.m_datp['2'] = glyf_2; shortfont.m_ln['2'] = sizeof(glyf_2); 
	shortfont.m_datp['3'] = glyf_3; shortfont.m_ln['3'] = sizeof(glyf_3); 
	shortfont.m_datp['4'] = glyf_4; shortfont.m_ln['4'] = sizeof(glyf_4); 
	shortfont.m_datp['5'] = glyf_5; shortfont.m_ln['5'] = sizeof(glyf_5); 
	shortfont.m_datp['6'] = glyf_6; shortfont.m_ln['6'] = sizeof(glyf_6); 
	shortfont.m_datp['7'] = glyf_7; shortfont.m_ln['7'] = sizeof(glyf_7); 
	shortfont.m_datp['8'] = glyf_8; shortfont.m_ln['8'] = sizeof(glyf_8); 
	shortfont.m_datp['9'] = glyf_9; shortfont.m_ln['9'] = sizeof(glyf_9); 
	// }}}

	// Special characters
	// {{{
	shortfont.m_datp[':'] = glyf_colon; shortfont.m_ln[':'] = sizeof(glyf_colon); 
	shortfont.m_datp[';'] = glyf_semicolon; shortfont.m_ln[';'] = sizeof(glyf_semicolon); 
	shortfont.m_datp['.'] = glyf_period; shortfont.m_ln['.'] = sizeof(glyf_period); 
	shortfont.m_datp[','] = glyf_comma; shortfont.m_ln[','] = sizeof(glyf_comma); 
	shortfont.m_datp['?'] = glyf_question; shortfont.m_ln['?'] = sizeof(glyf_question); 
	shortfont.m_datp[' '] = glyf_space; shortfont.m_ln[' '] = sizeof(glyf_space); 
	shortfont.m_datp['@'] = glyf_at; shortfont.m_ln['@'] = sizeof(glyf_at); 
	shortfont.m_datp['#'] = glyf_pound; shortfont.m_ln['#'] = sizeof(glyf_pound); 
	shortfont.m_datp['!'] = glyf_exclamation; shortfont.m_ln['!'] = sizeof(glyf_exclamation); 
	shortfont.m_datp['%'] = glyf_percent; shortfont.m_ln['%'] = sizeof(glyf_percent); 
	shortfont.m_datp['^'] = glyf_carat; shortfont.m_ln['^'] = sizeof(glyf_carat); 
	shortfont.m_datp['&'] = glyf_ampersand; shortfont.m_ln['&'] = sizeof(glyf_ampersand); 
	shortfont.m_datp['*'] = glyf_star; shortfont.m_ln['*'] = sizeof(glyf_star); 
	shortfont.m_datp['('] = glyf_left_paren; shortfont.m_ln['('] = sizeof(glyf_left_paren); 
	shortfont.m_datp[')'] = glyf_right_paren; shortfont.m_ln[')'] = sizeof(glyf_right_paren); 
	shortfont.m_datp['['] = glyf_left_bracket; shortfont.m_ln['['] = sizeof(glyf_left_bracket); 
	shortfont.m_datp[']'] = glyf_right_bracket; shortfont.m_ln[']'] = sizeof(glyf_right_bracket); 
	shortfont.m_datp['/'] = glyf_slash; shortfont.m_ln['/'] = sizeof(glyf_slash); 
	shortfont.m_datp['\\'] = glyf_backslash; shortfont.m_ln['\\'] = sizeof(glyf_backslash); 
	shortfont.m_datp['<'] = glyf_lt; shortfont.m_ln['<'] = sizeof(glyf_lt); 
	shortfont.m_datp['>'] = glyf_gt; shortfont.m_ln['>'] = sizeof(glyf_gt); 
	shortfont.m_datp['\''] = glyf_quote; shortfont.m_ln['\''] = sizeof(glyf_quote); 
	shortfont.m_datp['\"'] = glyf_double_quote; shortfont.m_ln['\"'] = sizeof(glyf_double_quote); 
	shortfont.m_datp['`'] = glyf_back_quote; shortfont.m_ln['`'] = sizeof(glyf_back_quote); 
	shortfont.m_datp['|'] = glyf_pipe; shortfont.m_ln['|'] = sizeof(glyf_pipe); 
	shortfont.m_datp['~'] = glyf_tilde; shortfont.m_ln['~'] = sizeof(glyf_tilde); 
	shortfont.m_datp['$'] = glyf_dollar; shortfont.m_ln['$'] = sizeof(glyf_dollar); 
	shortfont.m_datp['='] = glyf_equals; shortfont.m_ln['='] = sizeof(glyf_equals); 
	shortfont.m_datp['+'] = glyf_plus; shortfont.m_ln['+'] = sizeof(glyf_plus); 
	shortfont.m_datp['-'] = glyf_minus; shortfont.m_ln['-'] = sizeof(glyf_minus); 
	shortfont.m_datp['_'] = glyf_underscore; shortfont.m_ln['_'] = sizeof(glyf_underscore); 
	// }}}
}
