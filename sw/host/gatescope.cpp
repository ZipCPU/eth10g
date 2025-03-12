////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/gatescope.cpp
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

#ifndef	R_GATESCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a GATE scope within it.\n");
}
#else

#define	WBSCOPE		R_GATESCOPE
#define	WBSCOPEDATA	R_GATESCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

std::vector<unsigned>	crc_size, raw_size, raw_tx, tx_gate;

class	NETSCOPE : public SCOPE {
public:

	NETSCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~NETSCOPE(void) {}

	virtual	void	decode(DEVBUS::BUSW val) const {
		// {{{
		/*

		int	fault, src, countr, data, sync, stat_data;
		fault = (val >> 29) & 3;
		src   = (val >> 26) & 7;
		countr= (val >> 18) & 0x0ff;
		data  = (val >>  2) & 0x0ffff;
		sync  = (val      ) & 3;
		stat_data= (val >> 2) & 0x3ffff;

		printf("%8x %9s fault", countr,
			(fault == 3) ? "PHY"
			: (fault == 2) ? "Remote"
			: (fault == 1) ? "Local"
			: "No");
		*/
		// }}}
	}

	virtual	void	define_traces(void) {
		register_trace("pktgate_fill",   6,24);
		register_trace("fast_dbg_full",  1,23);
		register_trace("fast_dbg_valid", 1,22);
		register_trace("stat_gate_valid",1,21);
		register_trace("stat_tx_valid",  1,20);
		register_trace("r_full",         1,19);
		register_trace("abort_incoming", 1,18);
		register_trace("s_midpacket",    1,17);
		register_trace("lastv",          1,16);
		register_trace("output_active",  1,15);
		//
		register_trace("TRIGGER",        1,14);
		//
		register_trace("TXWD_VALID",     1,13);
		register_trace("TXWD_READY",     1,12);
		register_trace("TXWD_LAST",      1,11);
		register_trace("TXWD_ABORT",     1,10);
		register_trace("TXWD_BYTES",     3, 7);
		//
		register_trace("FULL_VALID",     1, 6);
		register_trace("FULL_READY",     1, 5);
		register_trace("FULL_LAST",      1, 4);
		register_trace("FULL_ABORT",     1, 3);
		register_trace("FULL_BYTES",     3, 0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	NETSCOPE *scope = new NETSCOPE(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(200000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("gatescope.vcd");
	}
}

#endif
