////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	cfgscope.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This file decodes the debug bits produced by the wbicapetwo.v
//		Verilog module, and stored in a Wishbone Scope.  It is useful
//	for determining if the scope works at all or not.  (The scope does work
//	... now ... and it turned out the most recent bugs were found in the
//	bus interconnect rather than the wbicapetwo module itself.  Still ...
//	the wbicapetwo module was updated with an adjustable clock, so
//	things always get better ... right?)
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

#ifndef	R_CFGSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a FAN scope within it.\n");
	exit(EXIT_FAILURE);
}
#else
#define	WBSCOPE		R_CFGSCOPE
#define	WBSCOPEDATA	R_CFGSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	CFGSCOPE : public SCOPE {
public:
	CFGSCOPE(DEVBUS *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, false, false) {};
	~CFGSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		int	clk, ckstb, ckstl,
			wbstb, wbstl, wback,
			csn, rdwrn, state,
			cfgin, cfgout;

		clk      = (val>>30)&1;
		ckstb    = (val>>29)&1;
		ckstl    = (val>>28)&1;
		wbstb    = (val>>27)&1;
		wback    = (val>>26)&1;
		csn      = (val>>25)&1;
		rdwrn    = (val>>24)&1;
		wbstl    = (val>>23)&1;
		state    = (val>>18)&0x1f;
		cfgin    = (val>> 8)&0x0ff;
		cfgout   = (val    )&0x0ff;

		printf("%s %s/%s  [%d%d%d] %2x [%02x - %02x]",
			(wbstb)?"STB":"   ",
			(wbstl)?"STL":"   ",
			(wback)?"ACK":"   ",
			clk, ckstb, ckstl,
			state, cfgin, cfgout);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	CFGSCOPE *scope = new CFGSCOPE(m_fpga, WBSCOPE, false);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("cfgscope.vcd");
	}
	delete	m_fpga;
}
#endif
