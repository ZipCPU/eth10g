////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/satadscope.cpp
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
#include <vector>

#include "regdefs.h"
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_SATADRPSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a SATA-RESET scope within it.\n");
}
#else

#define	WBSCOPE		R_SATADRPSCOPE
#define	WBSCOPEDATA	R_SATADRPSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	SATASCOPE : public SCOPE {
public:

	SATASCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~SATASCOPE(void) {}

	virtual	void	decode(DEVBUS::BUSW val) const {
		// {{{
		// }}}
	}

	virtual	void	define_traces(void) {
		register_trace("tx_fsm_state",     4, 27);
		//
		register_trace("qpll_refck_lost",  1, 26);
		//
		register_trace("wb_cyc",         1, 30);
		register_trace("wb_stb",         1, 29);
		register_trace("wb_we",          1, 28);
		register_trace("wb_stall",       1, 27);
		register_trace("wb_ack",         1, 26);
		register_trace("pll_drp_enable", 1, 25);
		register_trace("gtx_drp_enable", 1, 24);
		register_trace("drp_ack",        1, 23);
		register_trace("pll_drp_ready",  1, 22);
		register_trace("gtx_drp_ready",  1, 21);
		// register_trace("tx_watchdog_err",  1, 25);
		register_trace("drp_addr",       10,  0);
		register_trace("drp_data",       16,  0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	SATASCOPE *scope = new SATASCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("satapscope.vcd");
	}
}

#endif
