////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/softload.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Load software onto the flash.
//
//	1. Software is first loaded into DDR3 SDRAM.
//	2. uR0 = SRC address,		#1
//	3. uR1 = DST address,		#1
//	4. uR2 = Program length,	#1
//	5. uR3 = SRC address,		#2
//	6. uR4 = DST address,		#2
//	7. uR5 = Program length,	#2
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2026, Gisselquist Technology, LLC
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
#include <stdio.h>
#include <string.h>
#include "zipcpu.h"
#include "board.h"
#include "oledfont.h"
#include "oledfb.h"
#include "flashdev.h"
// }}}
//

void	load_image(const void *dst, const void *src, const unsigned ln) {
	fl_write((unsigned)dst, ln, src, 1);
}

int	main(int argc, char **argv) {
	int		uregs[16];
	int		src[2], dst[2], len[2];
	char		msg[128];
	unsigned	flags;
	unsigned	_rom, _sdram, _top_of_stack;

	// Load our context from the ZipLoader/environment
#ifdef	SAVE_CONTEXT
	save_context((int *)uregs);
#else
	GETUREG(uregs[0], "uR0");
	GETUREG(uregs[1], "uR1");
	GETUREG(uregs[2], "uR2");
	GETUREG(uregs[3], "uR3");
	GETUREG(uregs[4], "uR4");
	GETUREG(uregs[5], "uR5");
	GETUREG(uregs[6], "uR6");
	GETUREG(uregs[7], "uR7");
#endif
	src[0] = uregs[0];
	dst[0] = uregs[1];
	len[0] = uregs[2];
	src[1] = uregs[4];
	dst[1] = uregs[5];
	len[1] = uregs[6];
	flags  = uregs[7];

	if ((src[1] < _sdram)||(src[1] >= _top_of_stack))
		len[1] = 0;
	else if ((dst[1] < _rom)||(dst[1] >= _sdram))
		len[1] = 0;

	if ((src[0] < _sdram)||(src[0] >= _top_of_stack))
		len[0] = 0;
	else if ((dst[0] < _rom)||(dst[0] >= _sdram))
		len[0] = 0;

	if (0 == len[0] && 0 != len[1]) {
		src[0] = src[1];
		dst[0] = dst[1];
		len[0] = len[1];
		len[1] = 0;
	}

	init_tall_glyfs();
	init_short_glyfs();
	oled_hwsetup();
	fb_font = tallfontp;

	if (len[0])
		load_image((const char *)dst[0], (const char *)src[0], len[0]);
	if (len[1])
		load_image((const char *)dst[1], (const char *)src[1], len[1]);

	strcpy(msg, "Flash write complete");
	oled_write(msg);
	oled_flush();
	puts(msg);
}
