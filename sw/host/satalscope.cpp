////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/satalscope.cpp
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
// Copyright (C) 2025, Gisselquist Technology, LLC
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

#ifndef	R_SATALSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a SATA-LINK scope within it.\n");
}
#else

#define	WBSCOPE		R_SATALSCOPE
#define	WBSCOPEDATA	R_SATALSCOPED

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
		register_trace("link_state",  5, 26);
		register_trace("i_rx_valid",  1, 25);
		register_trace("i_phy_ready", 1, 24);
		register_trace("i_rx_primitive", 1, 23);
		register_trace("s_valid",     1, 22);
		register_trace("s_ready",     1, 21);
		register_trace("s_last",      1, 20);
		register_trace("s_abort",     1, 19);
		register_trace("s_success",   1, 18);
		register_trace("s_failed",    1, 17);
		register_trace("m_full",      1, 16);
		register_trace("m_empty",     1, 15);
		register_trace("m_last",      1, 14);
		register_trace("m_abort",     1, 13);
		register_trace("o_error",     1, 12);
		register_trace("o_ready",     1, 11);
		register_trace("rx_pdecode",  4,  7);
		register_trace("tx_pdecode",  4,  3);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	SATASCOPE *scope = new SATASCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(37500000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("satalscope.vcd");
	}
}

#endif
