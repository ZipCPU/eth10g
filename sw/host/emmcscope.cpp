////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/emmcscope.cpp
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

#ifndef	R_EMMCSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with an SDIO scope within it.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_EMMCSCOPE
#define	WBSCOPEDATA	R_EMMCSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	EMMCSCOPE : public SCOPE {
public:
	EMMCSCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~EMMCSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		// int	scl, sda;

		// scl = (val >> 13) & 1;
		// sda = (val >> 12) & 1;
		// printf("%3s %3s", (scl) ? "SCL":"", (sda) ? "SDA":"");
	}

	virtual	void	define_traces(void) {
		// OPT_IO=0 => neither SERDES or DDR
		//	= 1	=> DDR, but not SERDES
		//	= 2	=> SERDES
		//	= 3	=> Controller internals
		const unsigned	OPT_IO=2;

		switch(OPT_IO) {
		case 0:	// Neither SERDES nor DDR
			// {{{
			register_trace("trigger",   1,31);
			register_trace("i_sdclk",   1,25);
			register_trace("i_cmd_en",  1,23);
			register_trace("i_cmd_data",1,22);
			register_trace("i_cmd",     1,21);
			register_trace("w_cmd",     1,20);
			register_trace("r_cmd_strb",1,19);
			register_trace("r_cmd",     1,18);
			register_trace("dat_en",    1,17);
			register_trace("rx_strb",   1,16);
			register_trace("rx_data",   8, 8);
			register_trace("io_dat",    8, 0);
			break;
			// }}}
		case 1:	// DDR, but not SERDES
			// {{{
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
			// }}}
		case 2:	// SERDES
			// {{{
			register_trace("trigger",   1,31);

			register_trace("wait_for_busy",  1,29);
			register_trace("dat0_busy",      1,28);

			register_trace("i_cmd_en",       1,27);
			register_trace("i_cmd_tristate", 1,26);
			register_trace("cmd_data",       1,25);

			register_trace("data_tristate", 1,24);
			register_trace("tx_data",       4,20);

			register_trace("cmd_strb",      2,18);

			register_trace("i_rx_en",      1,15);
			register_trace("i_data_en",    1,14);
			register_trace("sync_ack",     1,13);
			register_trace("sync_nak",     1,12);

			register_trace("itok",      2, 10);
			register_trace("rx_strb",   2, 8);
			register_trace("rx_data",   8, 0);
			break;
			// }}}
		case 3:	// Controller (not PHY) internals
			// {{{
			register_trace("w_card_busy",    1, 30);
			//
			register_trace("o_cmd_request",  1, 29);
			register_trace("cmd_busy",       1, 28);
			register_trace("i_cmd_done",     1, 27);
			register_trace("i_cmd_err",      1, 26);
			register_trace("i_cmd_ercode",   2, 24);
			register_trace("i_cmd_response", 1, 23);
			//
			register_trace("i_dma_busy",     1, 22);
			register_trace("i_dma_err",      1, 21);
			register_trace("o_dma_abort",    1, 20);
			//
			register_trace("o_dma_sd2s",     1, 19);
			register_trace("o_sd2s_valid",   1, 18);
			register_trace("i_sd2s_ready",   1, 17);
			register_trace("o_sd2s_last",    1, 16);
			//
			register_trace("o_dma_s2sd",     1, 15);
			register_trace("i_s2sd_valid",   1, 14);
			register_trace("o_s2sd_ready",   1, 13);
			//
			register_trace("o_tx_mem_valid", 1, 12);
			register_trace("i_tx_mem_ready", 1, 11);
			register_trace("o_tx_mem_last",  1, 10);
			register_trace("o_tx_en",        1,  9);
			register_trace("tx_request",     1,  8);
			register_trace("tx_done",        1,  7);
			register_trace("tx_err",         1,  6);
			//
			register_trace("rx_mem_valid", 1, 5);
			register_trace("rx_done",      1, 4);
			register_trace("rx_err",       1, 3);
			register_trace("ercode",       1, 2);
			register_trace("rx_request",   1, 1);
			register_trace("o_rx_en",      1, 0);
			break;
			// }}}
		default:
			break;
		}
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	EMMCSCOPE *scope = new EMMCSCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("emmcscope.vcd");
	}
	delete	m_fpga;
}
#endif
