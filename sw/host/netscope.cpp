////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	netscope.cpp
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
//
// }}}
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "regdefs.h"
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_NETSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a NET scope within it.\n");
}
#else

#define	WBSCOPE		R_NETSCOPE
#define	WBSCOPEDATA	R_NETSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	NETSCOPE : public SCOPE {
public:
	NETSCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~NETSCOPE(void) {}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	trigger;

		trigger  = (val>>31)&1;
		if (!trigger) {
			int	abort, pkt, posn, ovw, lcl, rem, ln, cod,cw;
			rem   = (val >> 29) & 1;
			lcl   = (val >> 28) & 1;
			pkt   = (val >> 25) & 1;
			posn  = (val >> 18) & 3;
			abort = (val >> 17) & 1;
			ovw   = (val >> 16) & 1;
			cod   = (val) & 0x07ffffff;
			ln    = (val) & 0x01ffff;
			cw    = (cod >> 2) & 0x0ff;
			if (pkt) {
				printf("IDLE: %08x/%02x %s%s\n", cod, cw,
					(rem) ? "(REMOTE-FAULT)":"",
					(lcl) ? "(LOCAL-FAULT)":"");
			} else {
				printf("@%d PKT LN %5d %s%s",
					posn, ln,
					(ovw) ? "(COUNTER-OVERFLOW)":"",
					(abort) ? "(ABORTED)":"");
			}
		}
	}

	virtual	void	define_traces(void) {
		register_trace("remote_fault", 1,29);
		register_trace("local_fault",  1,28);
		register_trace("rx_fast_valid",1,27);
		register_trace("rx_valid",     1,26);
		register_trace("nopkt",        1,25);
		register_trace("posn",  2,18);
		register_trace("abort", 1,17);
		register_trace("ovw",   1,16);
		//
		register_trace("cw",     8,2);
		register_trace("cod",   24,0);
		register_trace("pkt_ln",17,0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	NETSCOPE *scope = new NETSCOPE(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("netscope.vcd");
	}
}

#endif
