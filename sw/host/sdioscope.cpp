////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdscope.cpp
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

#ifndef	R_SDIOSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with an SDIO scope within it.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_SDIOSCOPE
#define	WBSCOPEDATA	R_SDIOSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	SDIOSCOPE : public SCOPE {
public:
	SDIOSCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~SDIOSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		// int	scl, sda;

		// scl = (val >> 13) & 1;
		// sda = (val >> 12) & 1;
		// printf("%3s %3s", (scl) ? "SCL":"", (sda) ? "SDA":"");
	}

	virtual	void	define_traces(void) {
		// OPT_IO=0 => neither SERDES or DDR
		//	= 1	=> DDR, but not SERDES
		//	= 2	=> SERDES (not yet defined)
		const unsigned	OPT_IO=1;

		switch(OPT_IO) {
		case 0:
			register_trace("trigger",   1,31);
			register_trace("i_sdclk",   1,25);
			register_trace("i_cmd_en",  1,23);
			register_trace("i_cmd_data",1,22);
			register_trace("w_cmd",     1,20);
			register_trace("r_cmd_strb",1,19);
			register_trace("r_cmd",     1,18);
			register_trace("dat_en",    1,17);
			register_trace("rx_strb",   1,16);
			register_trace("rx_data",   8, 8);
			register_trace("io_dat",    8, 0);
			break;
		case 1:
			register_trace("trigger",   1,31);
			register_trace("i_rx_en",   1,28);
			register_trace("sample_ck", 2,26);
			register_trace("i_sdclk",   2,24);
			register_trace("i_cmd_en",  1,23);
			register_trace("i_cmd_data",2,21);
			register_trace("w_cmd",     1,20);
			register_trace("r_cmd_strb",1,19);
			register_trace("r_cmd",     1,18);
			register_trace("dat_en",    1,17);
			register_trace("rx_strb",   1,16);
			register_trace("rx_data",   8, 8);
			register_trace("io_dat",    8, 0);
			break;
		case 2:
			break;
		default:
			break;
		}
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	SDIOSCOPE *scope = new SDIOSCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("sdioscope.vcd");
	}
	delete	m_fpga;
}
#endif
