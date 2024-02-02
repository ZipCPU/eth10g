////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/flashscope.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This program decodes the bits in the debugging wires output
//		from the qflexpress module, and stored in the (compressed)
//	Wishbone Scope device.  The result is placed on the screen output, so
//	you can see what is going on internal to the device.
//		
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
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

#define	WBSCOPE		R_FLASHSCOPE
#define	WBSCOPEDATA	R_FLASHSCOPED

#define	SCOPEBIT(VAL,B)	((val >> B)&1)

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	QFLEXPRESSCOPE : public SCOPE {
	// While I put these in at one time, they really mess up other scopes,
	// since setting parameters based upon the debug word forces the decoder
	// to be non-constant, calling methods change, etc., etc., etc.
	//
	// int	m_oword[2], m_iword[2], m_p;
public:
	QFLEXPRESSCOPE(DEVBUS *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, true, vecread) {};
	~QFLEXPRESSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		int	cyc, cfg_stb, wb_stb, ack, stall, csn, sck, odat,
			qmod, idat, cfg_mode, cfg_speed, cfg_cs, cfg_dir,
			wb_we, wb_data; // actual_sck;

		cyc      = SCOPEBIT(val, 30);
		cfg_stb  = SCOPEBIT(val, 29);
		wb_stb   = SCOPEBIT(val, 28);
		ack      = SCOPEBIT(val, 27);
		stall    = SCOPEBIT(val, 26);
		csn      = SCOPEBIT(val, 25);
		sck      = SCOPEBIT(val, 24);
		odat     = (val>>20)&0x0f;
		qmod     = (val>>18)&0x03;
		idat     = (val>>14)&0x0f;
		cfg_mode = SCOPEBIT(val, 13);
		cfg_cs   = SCOPEBIT(val, 12);
		cfg_speed= SCOPEBIT(val, 11);
		cfg_dir  = SCOPEBIT(val, 10);
		// actual_sck= SCOPEBIT(val, 9);
		wb_we    = SCOPEBIT(val, 8);
		wb_data  = val & 0x0ff;

		printf("%3s%5s%5s%3s%4s%6s%3s%4s ",
			(cyc)?"CYC":"",
			(cfg_stb)?"CSTB":"",
			(wb_stb)?"DSTB":"",
			(wb_we)?"WE":"",
			(ack)?"AK":"",
			(stall)?"STALL":"",
			(!csn)?"CS":"",
			(sck)?"SCK":"");
		if (qmod == 0)
			printf("SPI  ");
		else if (qmod == 2)
			printf("WRITE");
		else if (qmod == 3)
			printf("READ ");
		else
			printf("UNK[%d] ", qmod);
		printf(" 0x%x %s 0x%x ", odat,
			(qmod== 0) ? "<->" : (qmod == 2) ? ">--" : "-->",
			idat);

		printf("B[%02x]", wb_data);
		if (cfg_mode)
			printf(" CFG[%s %s %s]",
				(cfg_cs)?"CS":"  ",
				(cfg_speed)?"HISPD":"     ",
				(cfg_dir)?"WR":"RD");
	}

	virtual	void define_traces(void) {
		register_trace("wb_cyc",      1, 30);
		register_trace("cfg_stb",     1, 29);
		register_trace("wb_stb",      1, 28);
		register_trace("wb_ack",      1, 27);
		register_trace("wb_stall",    1, 26);
		register_trace("o_cs_n",      1, 25);
		register_trace("o_sck",       1, 24);
		register_trace("o_qdat",      4, 20);
		register_trace("o_qmod",      2, 18);
		register_trace("i_qdat",      4, 14);
		register_trace("cfg_mode",    1, 13);
		register_trace("cfg_cs",      1, 12);
		register_trace("cfg_speed",   1, 11);
		register_trace("cfg_dir",     1, 10);
		register_trace("actual_sck",  1,  9);
		register_trace("wb_we",       1,  8);
		register_trace("wb_data",     8,  0);
	}
};

int main(int argc, char **argv) {
#ifndef	R_FLASHSCOPE
	printf(
"This design was not built with a flash scope attached to the QFLEXPRESS\n"
"design component.\n"
"\n"
"To use this design, create and enable a flash, and the QFLEXPRESS scope from\n"
"that.  To do this, you'll need to adjust the flash configuration file\n"
"used by AutoFPGA found in the auto-data/ directory, and then include it\n"
"within the Makefile of the same directory.\n");
#else
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	QFLEXPRESSCOPE *scope = new QFLEXPRESSCOPE(m_fpga, WBSCOPE, true);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("qflexpress.vcd");
	}
	delete	m_fpga;
#endif
}

