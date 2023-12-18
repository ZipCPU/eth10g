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
			state, // csn, rdwrn,
			cfgdat;

		clk      = (val>>30)&1;
		ckstb    = (val>>29)&1;
		ckstl    = (val>>28)&1;
		wbstb    = (val>>27)&1;
		wback    = (val>>26)&1;
		// csn      = (val>>25)&1;
		// rdwrn    = (val>>24)&1;
		wbstl    = (val>>23)&1;
		state    = (val>>18)&0x1f;
		cfgdat   = (val    )&0x0ffff;

		printf("%s %s/%s  [%d%d%d] %2x [%04x]",
			(wbstb)?"STB":"   ",
			(wbstl)?"STL":"   ",
			(wback)?"ACK":"   ",
			clk, ckstb, ckstl,
			state, cfgdat);
	}

	virtual	void	define_traces(void) {
		//
		register_trace("wb_stb",     1,31);
		register_trace("clk_stb",    1,30);
		register_trace("slow_clk",   1,29);
		register_trace("i_wb_stb",   1,27);
		register_trace("o_wb_ack",   1,26);
		register_trace("cfg_cs_n",   1,25);
		register_trace("cfg_rdwrn",  1,24);
		register_trace("o_wb_stall", 1,23);
		register_trace("state",      5,16);
		register_trace("cfg_data",  16, 0);
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
