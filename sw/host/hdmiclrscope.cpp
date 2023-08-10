////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmiclrscope.cpp
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

	virtual	void	decode(DEVBUS::BUSW val) const {
		unsigned	cloc, mloc, sync, vld, px;
		static	 unsigned	lpx = 0;

		cloc = (val >> 26) & 0x0f;
		mloc = (val >> 22) & 0x0f;
		sync = (val >> 12) & 0x03ff;
		vld  = (val >> 11) & 0x03ff;
		px   =  val        & 0x03ff;

		lpx = (lpx << 10) | px;

		printf("%x %x S:%03x %s %s P:%03x L:%08x", cloc, mloc, sync,
			(sync != 0) ? "SYNC":"    ",
			(vld) ? "VLD":"   ", px, lpx);
	}

	virtual	void	define_traces(void) {
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
