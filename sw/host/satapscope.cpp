////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/satapscope.cpp
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

#ifndef	R_SATAPSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a SATA-RESET scope within it.\n");
}
#else

#define	WBSCOPE		R_SATAPSCOPE
#define	WBSCOPEDATA	R_SATAPSCOPED

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
		register_trace("rx_cdrhold",       1, 25);
		// register_trace("tx_watchdog_err",  1, 25);
		register_trace("tx_user_ready",    1, 24);
		register_trace("tx_ready",         1, 23);
		//
		register_trace("o_gtx_reset",      1, 22);
		register_trace("o_pll_reset",      1, 21);
		register_trace("o_err",            1, 20);
		register_trace("o_user_ready",     1, 19);
		register_trace("o_complete",       1, 18);
		register_trace("fsm_zero",         1, 17);
		register_trace("watchdog_timeout", 1, 16);
		register_trace("i_power_down",     1, 15);
		register_trace("r_cdr_zerowait",   1, 14);
		register_trace("valid_clock",      1, 13);
		register_trace("gtx_reset_done",   1, 12);
		register_trace("pll_locked",       1, 11);
		register_trace("fsm_counter",      7,  4);
		register_trace("rx_fsm_state",     4,  0);
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
