////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	smiscope.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This file decodes the debug bits produced by the SMI IP and
//		stored in a (compressed) WB scope.  It is useful for determining
//	if the SMI IP is working, or even if/how the RPi is toggling the
//	associated SMI bits.
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
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_SMISCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a NET scope within it.\n");
}
#else

#define	WBSCOPE		R_SMISCOPE
#define	WBSCOPEDATA	R_SMISCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	SMISCOPE : public SCOPE {
public:
	SMISCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~SMISCOPE(void) {}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	trigger;

		trigger  = (val>>31)&1;

		printf("%6s", (trigger) ? "TRIG! ":"");

		printf("%3s ",  ((val>>28)&1) ? "OEN":"");
		printf("%2s ",  ((val>>27)&1) ? "WEN":"");
		printf("A[%02x] ", ((val>>18)&0x03f));
		printf("D[%05x] ", (val&0x03ffff));
	}

	virtual	void	define_traces(void) {
		//
		register_trace("o_smi_oen",1,30);
		register_trace("last",     1,29);
		register_trace("ck_oen",   1,28);
		register_trace("ck_wen",   1,27);
		//
		register_trace("fif_err",  1,26);
		register_trace("ifif_full",1,25);
		register_trace("ofif_empty", 1,24);
		register_trace("i_smi_sa",6,18);
		//
		register_trace("io_smi_data",18,0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	SMISCOPE *scope = new SMISCOPE(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("smiscope.vcd");
	}
}

#endif
