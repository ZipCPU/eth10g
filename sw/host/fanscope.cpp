////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	fanscope.cpp
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
#include <design.h>
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_FANSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a FAN scope within it.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_FANSCOPE
#define	WBSCOPEDATA	R_FANSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	FANSCOPE : public SCOPE {
public:
	FANSCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~FANSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		int	scl, sda;

		// scl = (val >> 13) & 1;
		// sda = (val >> 12) & 1;
		scl = (val >> 30) & 1;
		sda = (val >> 29) & 1;
		printf("%3s %3s", (scl) ? "SCL":"", (sda) ? "SDA":"");
	}

	virtual	void	define_traces(void) {
		register_trace("i2c_abort",  1,29);
		register_trace("i2c_stretch",1,28);
		register_trace("half_insn", 4,24);
		register_trace("r_wait",    1,23);
		register_trace("soft_half", 1,22);
		register_trace("r_aborted", 1,21);
		register_trace("r_err",     1,20);
		register_trace("r_halted",  1,19);
		register_trace("insn_valid",1,18);
		register_trace("half_valid",1,17);
		register_trace("imm_cycle", 1,16);
		register_trace("o_scl",     1,15);
		register_trace("o_sda",     1,14);
		register_trace("i_scl",     1,13);
		register_trace("i_sda",     1,12);
		register_trace("insn", 12,0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	FANSCOPE *scope = new FANSCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("fanscope.vcd");
	}
	delete	m_fpga;
}
#endif
