////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	byteswap.h
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
// }}}
#ifndef	BYTESWAP_H
#define	BYTESWAP_H

#include <stdint.h>

/*
 * The byte swapping routines below are designed to support conversions from a
 * little endian machine/host (such as my PC) to the big endian byte order used
 * on the ZipCPU.  If the current machine is already little endian, no byte
 * swapping is required.
 */
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
/*
 * byteswap
 *
 * Given a big (or little) endian word, return a little (or big) endian word.
 */
extern	uint32_t
byteswap(uint32_t v);

/*
 * byteswapbuf
 *
 * To swap from the byte order of every 32-bit word in the given buffer.
 */
extern	void	byteswapbuf(int ln, uint32_t *buf);

#else
#define	byteswap(A)		 (A)
#define	byteswapbuf(A, B)
#endif

/*
 * buildword
 *
 * Given a pointer within an array of characters, build a 32-bit big-endian
 * word from those characters.  Does not require the character pointer to be
 * aligned.
 */ 
extern	uint32_t buildword(const unsigned char *p);

/*
 * buildswap
 *
 * Same as buildword, except that we build a little endian word from the
 * characters given to us.  Hence the first character is the low order octet
 * of the word.
 */
extern	uint32_t buildswap(const unsigned char *p);

#endif
