////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	cpunetscope.cpp
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
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_CPUNETSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a NET scope within it.\n");
}
#else

#define	WBSCOPE		R_CPUNETSCOPE
#define	WBSCOPEDATA	R_CPUNETSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	CPUNETSCOPE : public SCOPE {
public:
	CPUNETSCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~CPUNETSCOPE(void) {}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	trigger;

		trigger  = (val>>31)&1;
		if (!trigger) {
			int	cyc, stb, we, stall, ack, err;

			printf("ST:R%1d,W%1d ", (val >> 22)&3, (val >> 24)&7);

			cyc = (val >> 16);
			err   = (cyc &  1);
			ack   = (cyc &  2) >> 1;
			stall = (cyc &  4) >> 2;
			we    = (cyc &  8) >> 3;
			stb   = (cyc & 16) >> 4;
			cyc   = (cyc & 32) >> 5;

			printf("O: %3s%3s %2s %5s %3s%3s",
				cyc   ? "CYC":"",
				stb   ? "STB":"",
				we    ? "WE":"",
				stall ? "STALL":"",
				ack   ? "ACK":"",
				err   ? "ERR":"");

			cyc = (val >> 8);
			err   = (cyc &  1);
			ack   = (cyc &  2) >> 1;
			stall = (cyc &  4) >> 2;
			we    = (cyc &  8) >> 3;
			stb   = (cyc & 16) >> 4;
			cyc   = (cyc & 32) >> 5;

			printf("WR: %3s%3s %2s %5s %3s%3s",
				cyc   ? "CYC":"",
				stb   ? "STB":"",
				we    ? "WE":"",
				stall ? "STALL":"",
				ack   ? "ACK":"",
				err   ? "ERR":"");

			cyc = val;
			err   = (cyc &  1);
			ack   = (cyc &  2) >> 1;
			stall = (cyc &  4) >> 2;
			we    = (cyc &  8) >> 3;
			stb   = (cyc & 16) >> 4;
			cyc   = (cyc & 32) >> 5;

			printf("RD: %3s%3s %2s %5s %3s%3s",
				cyc   ? "CYC":"",
				stb   ? "STB":"",
				we    ? "WE":"",
				stall ? "STALL":"",
				ack   ? "ACK":"",
				err   ? "ERR":"");

		}
	}

	virtual	void	define_traces(void) {
		register_trace("wr_state",    3,24);
		register_trace("rd_state",    2,22);

		register_trace("o_wb_cyc",    1,21);
		register_trace("o_wb_stb",    1,20);
		register_trace("o_wb_we",     1,19);
		register_trace("i_wb_stall",  1,18);
		register_trace("i_wb_ack",    1,17);
		register_trace("i_wb_err",    1,16);

		register_trace("wr_wb_cyc",   1,13);
		register_trace("wr_wb_stb",   1,12);
		register_trace("wr_wb_we",    1,11);
		register_trace("wr_wb_stall", 1,10);
		register_trace("wr_wb_ack",   1, 9);
		register_trace("wr_wb_err",   1, 8);

		register_trace("rd_wb_cyc",   1, 5);
		register_trace("rd_wb_stb",   1, 4);
		register_trace("rd_wb_we",    1, 3);
		register_trace("rd_wb_stall", 1, 2);
		register_trace("rd_wb_ack",   1, 1);
		register_trace("rd_wb_err",   1, 0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	CPUNETSCOPE *scope = new CPUNETSCOPE(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("cpunetscope.vcd");
	}
}

#endif
