////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/cputest.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Verify that all of the LEDs work, and in particular LED #0.
//		LED #0 is special, since it didn't work in initial testing.
//	Therefore we'll constantly blink it.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2026, Gisselquist Technology, LLC
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
// }}}
#include <stdint.h>
#include "board.h"
#include "zipcpu.h"
#include "zipsys.h"

int	main(int argc, char **argv) {
	unsigned	fsm = 0, step = 0;
#ifdef	R_RTCCOUNT
	unsigned	now, last;
	now = last = _rtccount;
#else
	_zip->z_tma = TMR_INTERVAL | 50000000;
	_zip->z_pic = DALLPIC;
	_zip->z_pic = EINT(SYSINT_TMA);
#endif
	while(1) {
		step = 0;
#ifdef	R_RTCCOUNT
		last = now; now = _rtccount;
		step = (last ^ now) >> 31;
#else
		step = (_zip->z_pic & SYSINT_TMA) ? 1:0;
		_zip->z_pic = SYSINT_TMA;
#endif
		if (!step)
			continue;

		fsm++; fsm &= 0x01f;
		if (fsm & 1)
			// Shut all LEDs off
			(*_spio) = 0x0ff01;
		else switch(fsm >> 1) {
		case 0: (*_spio) = 0x0ff02; break;
		case 1: (*_spio) = 0x0ff04; break;
		case 2: (*_spio) = 0x0ff08; break;
		case 3: (*_spio) = 0x0ff10; break;
		case 4: (*_spio) = 0x0ff20; break;
		case 5: (*_spio) = 0x0ff40; break;
		case 6: (*_spio) = 0x0ff80; break;
		default:
			(*_spio) = 0x0ff00; break;
		}
	}
}

