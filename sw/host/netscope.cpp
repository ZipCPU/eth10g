////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	netscope.cpp
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
#include <vector>

#include "regdefs.h"
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_NETSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with a NET scope within it.\n");
}
#else

#define	WBSCOPE		R_NETSCOPE
#define	WBSCOPEDATA	R_NETSCOPED

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
		int	trigger;

		trigger  = (val>>31)&1;
		if (!trigger) {
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

			switch(src) {
			case 0: printf(", IDLE"); break;
			case 1: printf(", CTRL %04x-%d", data, sync); break;
			case 2: printf(", SOP  %04x-%d", data, sync); break;
			case 3: printf(", EOP  %04x-%d", data, sync); break;
			case 4: printf(", RX  : %05x", stat_data);   raw_size.push_back(stat_data); break;
			case 5: printf(", CRC : %05x", stat_data);  crc_size.push_back(stat_data); break;
			case 6: printf(", TX  : %05x", stat_data);   raw_tx.push_back(stat_data); break;
			case 7: printf(", GATE: %05x", stat_data); tx_gate.push_back(stat_data); break;
			default: break;
			}
		}
	}

	virtual	void	define_traces(void) {
		register_trace("local_stat", 2,29);
		register_trace("source",  3,26);
		register_trace("counter", 8,18);
		register_trace("data",   16, 2);
		register_trace("sync",    2, 0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	NETSCOPE *scope = new NETSCOPE(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("netscope.vcd");

		for(unsigned k=0; k< raw_size.size(); k++) {
			printf("RX Packet LN: %08x\n",  raw_size[k]);
		} for(unsigned k=0; k< crc_size.size(); k++) {
			printf("RX/CRC PktLN: %08x\n",  crc_size[k]);
		} for(unsigned k=0; k< raw_tx.size(); k++) {
			printf("TX Packet LN: %08x\n",  raw_tx[k]);
		} for(unsigned k=0; k< tx_gate.size(); k++) {
			printf("TX Pkt Gate :: %08x\n",  tx_gate[k]);
		}
	}
}

#endif
