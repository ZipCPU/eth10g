////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/busscope.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This program decodes the some of the bits across several WB
//		busses within the design, to find out where bus errors are
//	getting generated from.
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
//
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "port.h"
#include "regdefs.h"
#include "scopecls.h"
#include "ttybus.h"
// }}}

#define	WBSCOPE		R_BUSSCOPE
#define	WBSCOPEDATA	R_BUSSCOPED

#define	SCOPEBIT(VAL,B)	((val >> B)&1)

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	BUSSCOPE : public SCOPE {
	// While I put these in at one time, they really mess up other scopes,
	// since setting parameters based upon the debug word forces the decoder
	// to be non-constant, calling methods change, etc., etc., etc.
	//
	// int	m_oword[2], m_iword[2], m_p;
public:
	BUSSCOPE(DEVBUS *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, true, vecread) {};
	~BUSSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
	}

	virtual	void define_traces(void) {
		register_trace("watchdog",   1, 24);
		//
		register_trace("wbu_cyc",    1, 23);
		register_trace("wbu_stb",    1, 22);
		register_trace("wbu_we",     1, 21);
		register_trace("wbu_stall",  1, 20);
		register_trace("wbu_ack",    1, 19);
		register_trace("wbu_err",    1, 18);
		//
		register_trace("zip_cyc",    1, 17);
		register_trace("zip_stb",    1, 16);
		register_trace("zip_we",     1, 15);
		register_trace("zip_stall",  1, 14);
		register_trace("zip_ack",    1, 13);
		register_trace("zip_err",    1, 12);
		//
		register_trace("down_cyc",   1, 11);
		register_trace("down_stb",   1, 10);
		register_trace("down_we",    1,  9);
		register_trace("down_stall", 1,  8);
		register_trace("down_ack",   1,  7);
		register_trace("down_err",   1,  6);
		//
		register_trace("ddr3_cyc",   1,  5);
		register_trace("ddr3_stb",   1,  4);
		register_trace("ddr3_we",    1,  3);
		register_trace("ddr3_stall", 1,  2);
		register_trace("ddr3_ack",   1,  1);
		register_trace("ddr3_err",   1,  0);
	}
};

int main(int argc, char **argv) {
#ifndef	R_BUSSCOPE
	printf(
"This design was not built with a bus scope within it.\n"
"\n"
"To use this software, enable the bus scope at the main level.  To do this,\n"
"you'll need to include the bus scope configuration file used by AutoFPGA\n"
"found in the auto-data/ directory, within the Makefile of the same\n"
"directory.\n");
#else
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	BUSSCOPE *scope = new BUSSCOPE(m_fpga, WBSCOPE, true);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("busscope.vcd");
	}
	delete	m_fpga;
#endif
}

