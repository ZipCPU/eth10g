////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/byteswap.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To convert between little endian and big endian byte orders,
//		and to handle conversions between character strings and
//	bit-endian words made from those characters.
//
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
#include "byteswap.h"

/*
 * byteswap
 * {{{
 * Given a big (or little) endian word, return a little (or big) endian word.
 */
uint32_t
byteswap(uint32_t v) {
	uint32_t	r = 0;

	r = (v & 0x0ff);
	r <<= 8; v >>= 8;
	r |= (v & 0x0ff);
	r <<= 8; v >>= 8;
	r |= (v & 0x0ff);
	r <<= 8; v >>= 8;
	r |= (v & 0x0ff);

	return r;
}
// }}}

/*
 * byteswapbuf
 * {{{
 * To swap from the byte order of every 32-bit word in the given buffer.
 */
void
byteswapbuf(int ln, uint32_t *buf) {
	for(int i=0; i<ln; i++)
		buf[i] = byteswap(buf[i]);
}
// }}}

/*
 * buildword
 * {{{
 * Given a pointer within an array of characters, build a 32-bit big-endian
 * word from those characters.  Does not require the character pointer to be
 * aligned.
 */
uint32_t
buildword(const unsigned char *p) {
	uint32_t	r = 0;

	r  = (*p++); r <<= 8;
	r |= (*p++); r <<= 8;
	r |= (*p++); r <<= 8;
	r |= (*p  );

	return r;
}
// }}}

/*
 * buildswap
 * {{{
 * Same as buildword, except that we build a little endian word from the
 * characters given to us.  Hence the first character is the low order octet
 * of the word.
 */
uint32_t
buildswap(const unsigned char *p) {
	uint32_t	r = 0;

	r  = p[3]; r <<= 8;
	r |= p[2]; r <<= 8;
	r |= p[1]; r <<= 8;
	r |= p[0];

	return r;
}
// }}}

