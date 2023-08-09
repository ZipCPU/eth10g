////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rxedidscope.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To communicate with a generic scope, specifically the one for
//		testing the I2C communication path associated with an EDID
//	data set.  Further, this file defines what the various wires are
//	on that path, as well as the fact that the scope is compressed.
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
// }}}
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

#include "regdefs.h"
#include <design.h>
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_RXEDIDSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a I2C scope within it.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_RXEDIDSCOPE
#define	WBSCOPEDATA	R_RXEDIDSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	RXEDIDSCOPE : public SCOPE {
public:
	RXEDIDSCOPE(DEVBUS *fpga, unsigned addr, bool vecread=true)
		: SCOPE(fpga, addr, true, vecread) {};
	~RXEDIDSCOPE(void) {}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	i_rx_sck, i_rx_sda, o_rx_sck, o_rx_sda;

		i_rx_sck = (val>>3)&1;
		i_rx_sda = (val>>2)&1;
		o_rx_sck = (val>>1)&1;
		o_rx_sda = (val   )&1;

		printf("RX-CMD[%s %s] TX-CMD[%s %s]",
			(o_rx_sck)?"SCK":"   ", (o_rx_sda)?"SDA":"   ",
			(i_rx_sck)?"SCK":"   ", (i_rx_sda)?"SDA":"   ");
	}

	virtual	void	define_traces(void) {
		//
		register_trace("i_wb_stb",  1, 27);
		register_trace("o_wb_we",   1, 26);
		register_trace("o_wb_stall",1, 25);
		register_trace("o_wb_ack",  1, 24);
		register_trace("i_wb_addr", 6, 18);
		//
		register_trace("s_valid", 1, 15);
		register_trace("s_ready", 1, 14);
		register_trace("s_last",  1, 13);
		register_trace("s_data",  8, 4);
		//
		register_trace("i_rx_scl", 1, 3);
		register_trace("i_rx_sda", 1, 2);
		register_trace("o_rx_scl", 1, 1);
		register_trace("o_rx_sda", 1, 0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	RXEDIDSCOPE *scope = new RXEDIDSCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("rxedidscope.vcd");
	}
	delete	m_fpga;
}
#endif
