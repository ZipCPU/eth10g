////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/hdmiclrscope.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To communicate with a generic scope, specifically the one for
//		capturing one (or more) lines of an TMDS & 8b/10b encoded HDMI
//	color as it is being synchronized to.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
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
//
//
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "regdefs.h"
#include <design.h>
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_HDMICLRSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with an HDMI color.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_HDMICLRSCOPE
#define	WBSCOPEDATA	R_HDMICLRSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	HDMICLRSCOPE : public SCOPE {
public:
	HDMICLRSCOPE(DEVBUS *fpga, unsigned addr, bool vecread=true)
		: SCOPE(fpga, addr, false, vecread) {};
	~HDMICLRSCOPE(void) {}

	const int SCOPETYPE = 3;

	virtual	void	decode(DEVBUS::BUSW val) const {
		switch(SCOPETYPE) {
		case 0: {
			unsigned	cloc, mloc, sync, vld, px;
			static	 unsigned	lpx = 0;

			cloc = (val >> 26) & 0x0f;
			mloc = (val >> 22) & 0x0f;
			sync = (val >> 12) & 0x03ff;
			vld  = (val >> 11) & 0x03ff;
			px   =  val        & 0x03ff;

			lpx = (lpx << 10) | px;

			printf("%x %x S:%03x %s %s P:%03x L:%08x",
				cloc, mloc, sync,
				(sync != 0) ? "SYNC":"    ",
				(vld) ? "VLD":"   ", px, lpx);
			} break;
		case 1: {
			unsigned	r, g, b, h, v, vld, sr, sg, sb;

			sr =(val >> 26) & 0x01;
			sg = (val >> 25) & 0x01;
			sb = (val >> 24) & 0x01;
			vld=(val >> 26) & 0x01;
			v = (val >> 25) & 0x01;
			h = (val >> 24) & 0x01;
			r = (val >> 16) & 0x0ff;
			g = (val >>  8) & 0x0ff;
			b = (val      ) & 0x0ff;
			printf("%s %s %s %2s%3d %2s%3d %2s%3d\n",
				vld ? "VLD":"   ",
				v ? "VSYNC":"     ",
				h ? "HSYNC":"     ",
				sr ? "S:":"  ", r,
				sg ? "S:":"  ", g,
				sb ? "S:":"  ", b);
			} break;
		case 2: {
			unsigned	r, g, b, gs, rs;

			rs= (val >> 31) & 0x01;
			gs= (val >> 30) & 0x01;
			r = (val >> 20) & 0x03ff;
			g = (val >> 10) & 0x03ff;
			b = (val      ) & 0x03ff;
			printf("%s%03x %s%03x   %03x",
				(rs) ? "S:":"  ", r,
				(gs) ? "S:":"  ", g,
				b);
			} break;
		case 3: {
			unsigned	r, g, b, vld, rdy, h, v;

			vld = (val >> 27) & 0x01;
			rdy = (val >> 26) & 0x01;
			h   = (val >> 25) & 0x01;
			v   = (val >> 24) & 0x01;
			r   = (val >> 16) & 0x0ff;
			g   = (val >>  8) & 0x0ff;
			b   = (val      ) & 0x0ff;
			printf("%s %s %02x,%02x,%02x %s %s",
				(vld) ? "VALID":"     ",
				(rdy) ? "READY":"     ",
				r, g, b,
				(h) ? "EOL":"   ",
				(v) ? "EOF":"   ");
			} break;
		}
	}

	virtual	void	define_traces(void) {
		switch(SCOPETYPE) {
		case 0: {
			//
			register_trace("trigger",           1, 31);
			register_trace("sync_valid",        1, 30);
			register_trace("chosen_match_loc",  4, 26);
			//
			register_trace("match_loc",  4, 22);
			register_trace("full_sync", 10, 12);
			register_trace("match",      1, 11);
			register_trace("sync",       1, 10);
			register_trace("i_px",      10,  0);
			} break;
		case 1: {
			register_trace("start", 1, 31);
			//
			register_trace("control_sync",1, 30);
			register_trace("start_red",   1, 29);
			register_trace("start_green", 1, 28);
			register_trace("start_blue",  1, 27);
			register_trace("valid", 1, 26);
			register_trace("vsync", 1, 25);
			register_trace("hsync", 1, 24);
			register_trace("red",   8, 16);
			register_trace("green", 8,  8);
			register_trace("blue",  8,  0);
			} break;
		case 2: {
			register_trace("start_red",   1, 31);
			register_trace("start_green", 1, 30);
			register_trace("red",   10, 20);
			register_trace("green", 10, 10);
			register_trace("blue",  10,  0);
			} break;
		case 3:
		default: {
			register_trace("eof",     1, 30);
			register_trace("alpha",   2, 28);
			register_trace("valid",   1, 27);
			register_trace("ready",   1, 26);
			register_trace("hlast",   1, 25);
			register_trace("vlast",   1, 24);
			register_trace("red",   8, 16);
			register_trace("green", 8,  8);
			register_trace("blue",  8,  0);
			} break;
		};
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	HDMICLRSCOPE *scope = new HDMICLRSCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(148500000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("hdmiclrscope.vcd");
	}
	delete	m_fpga;
}
#endif
