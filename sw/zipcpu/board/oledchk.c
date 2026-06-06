////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/oledchk.c
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
//
#include <stdint.h>
#include <stdio.h>
#include "board.h"
#include "txfns.h"
#include "zipcpu.h"
#include "zipsys.h"
#include "oledfont.h"
#include "oledfb.h"
// }}}

int gen_message(unsigned msgid) {
	extern		OLED_FB *fb;
	unsigned	counts;
	char		sbuf[16], *msg = NULL;

	oled_clear();
	fb_font = tallfontp;
	switch(msgid & 0x1f) {
	case 0: fb_font = shortfontp;
		oled_write("Network clock rate");
		oled_move(5, 1);
		counts = _netclk[4];
		sprintf(sbuf, "%8.4f MHz", counts / 1e6);
		oled_write(sbuf);
		//
		oled_move(0, 2);
		oled_write("Reference clock rate");
		oled_move(5, 3);
		counts = _netclk[5];
		sprintf(sbuf, "%8.4f MHz", counts / 1e6);
		oled_write(sbuf);
		break;
	case 1:
		msg = "HEY ALEX!";
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 2:	msg = "Yoohoo!";
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 3:	msg = "Is anyone home?";
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 4: fb_font = shortfontp;
		msg = "Parlez vous francais";
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 5:
		oled_write("sprechen sie");	// 161--too long
		oled_move(5,2);
		oled_write("deutsch?");	// 161--too long
		break;
	case 6:
		oled_write("Anyone speak");
		oled_move(5,2);
		oled_write("pixel?");	
		break;
	case 7:	msg = "What\'s up doc?";			// 110
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 8:	oled_write("You\'re");
		oled_move(5,2);
		oled_write("dethshpickable");			//
		break;
	case 9:	oled_write("Is that a");			//
		oled_move(5,2); oled_write("weapon?");
		break;
	case 10: msg = "Wipeout!";
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 11: msg = "I\'m such a genius!";	// 113
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 12: msg = "Doh!";			// 103?
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 13:
		oled_write("Houston, we have");
		oled_move(5,2);
		oled_write("a problem");			// 161--too long
		break;
	case 14:
		oled_write("General");
		oled_move(5,2);
		oled_write("quarters!");
		break;
	case 15: msg = "You rang?";		// 110
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 16: msg = "I\'ll be back";		// 56,2 ??
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 17: msg = "Clear the bridge";		// 120
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 18:
		oled_write("Computers can");
		oled_move(5,2);
		oled_write("do that?");	// 177
		break;
	case 19:
		oled_write("I\'m assuming");	// 148
		oled_move(5,2);
		oled_write("command here");	// 148
		break;
	case 20: msg = "Fascinating";		// 103
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 21:
		oled_write("Computers can");	// 177
		oled_move(5,2);
		oled_write("do that?");	// 177
		break;
	case 22:
		// oled_write("There\'s something screwey round here");//277
		msg = "Yes, my lord";
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 23: msg = "Hey, hey, hey!";		// 94
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 24:
		oled_write("Danger will");	// 154
		oled_move(5,2);
		oled_write("robinson!");	// 154
		break;
	case 25:
		oled_write("Have you lost"); // 262
		oled_move(5,2);
		oled_write("your mind?"); // 262
		break;
	case 26:
		oled_write("Now looky, I");	// 200
		oled_move(5,2);
		oled_write("say looky here!");	// 200
		break;
	case 27:msg = "Nevermind!";	// 74
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 28:
		oled_write("Command functions");
		oled_move(5,2);
		oled_write("are offline");	// 214
		break;
	case 29:
		msg = "It's showtime!";	// 97
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	case 30:
		oled_write("Somebody");
		oled_move(5,2);
		oled_write("stop me!");
		break;

	case 31: msg = "That's all folks!";	// 124
		oled_write(msg);
		txstr(msg); txstr("\n");
		break;
	default: break;
	} oled_flush();
}

int main(int argc, char **argv) {
	unsigned	fsm = 0, step = 0, msg_count = 0;
#ifdef	R_RTCCOUNT
	unsigned	now, last;
	now = last = _rtccount;
#else
	_zip->z_tma = TMR_INTERVAL | 50000000;
	_zip->z_pic = DALLPIC;
	_zip->z_pic = EINT(SYSINT_TMA);
#endif
	init_tall_glyfs();
	init_short_glyfs();
	oled_hwsetup();
	fb_font = tallfontp;
	// set_fixed(tallfontp);

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
		if (fsm & 1) {
			// Shut all LEDs off
			(*_spio) = 0x0ff01;
			gen_message(0);
			// gen_message(msg_count++);
		} else switch(fsm >> 1) {
		case 0: (*_spio) = 0x0ff02;
			gen_message(msg_count++);
			break;
		case 1: (*_spio) = 0x0ff04; break;
		case 2: (*_spio) = 0x0ff08; break;
		case 3: (*_spio) = 0x0ff10; break;
		case 4: (*_spio) = 0x0ff20; break;
		case 5: (*_spio) = 0x0ff40; break;
		case 6: (*_spio) = 0x0ff80; break;
		default:
			gen_message(0);
			(*_spio) = 0x0ff00; break;
		}
	}
}
