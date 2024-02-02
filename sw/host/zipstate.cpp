////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/zipstate.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To get a quick (understandable) peek at what the ZipCPU
//		is up to without stopping the CPU.  This is basically
//	identical to a "wbregs cpu" command, save that the bit fields of the
//	result are broken out into something more human readable.
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
// }}}
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "port.h"
#include "llcomms.h"
#include "regdefs.h"
#include "ttybus.h"

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

/*
unsigned int	cmd_read(FPGA *fpga, int r) {
	const unsigned int	MAXERR = 1000;
	unsigned int	errcount = 0;
	unsigned int	s;

	return	fpga->readio(R_ZIPCTRL, CPU_REGBASE + (r*4));
}
*/

void	read_regs(DEVBUS *fpga, unsigned *r) {
	fpga->readi(R_ZIPREGS, 32, r);
}

void	usage(void) {
	printf("USAGE: zipstate\n");
}

int main(int argc, char **argv) {
	bool	long_state = false;
	unsigned int	v;
	int	skp;

	skp=1;
	for(int argn=0; argn<argc-skp; argn++) {
		if (argv[argn+skp][0] == '-') {
			if (argv[argn+skp][1] == 'l')
				long_state = true;
			skp++; argn--;
		} else
			argv[argn] = argv[argn+skp];
	} argc -= skp;

	m_fpga = connect_devbus(NULL);

	if (!long_state) {
		v = m_fpga->readio(R_ZIPCTRL);

		printf("0x%08x: ", v);
		if (v & 0x0008) printf("RESET ");
		if (v & 0x0400) printf("PINT ");
		// if (v & 0x0100) printf("STEP "); // self resetting
		// if (v & 0x00200) printf("DBG-STALL ");
		if (v & 0x0001) {
			if (v & 0x002)
				printf("DBG-HALTED ");
			else
				printf("HALT_REQ ");
		}
		// if (v & 0x0800) printf("CLR-CACHE ");
		if ((v & 0x0300)==0x0100) {
			printf("SW-HALTED");
		} else {
			if (v & 0x0100) printf("SLEEPING ");
			if (v & 0x0200) printf("GIE(UsrMode) ");
		}
		// if (v & 0x04000) printf("sBusErr ");
		if (v & 0x0800) printf("BREAK-HALT");

		// if ((v & 0x0fc00) == 0) printf("Running");
		printf("\n");
	} else {
		unsigned	r[32];

		printf("Reading the long-state ...\n"); fflush(stdout);
		read_regs(m_fpga, r);
		for(int i=0; i<14; i++) {
			printf("sR%-2d: 0x%08x ", i, r[i]);
			if ((i&3)==3)
				printf("\n");
		} printf("sCC : 0x%08x ", r[14]);
		printf("sPC : 0x%08x ", r[15]);
		printf("\n\n"); 

		for(int i=0; i<14; i++) {
			printf("uR%-2d: 0x%08x ", i, r[i+16]);
			if ((i&3)==3)
				printf("\n");
		} printf("uCC : 0x%08x ", r[30]);
		printf("uPC : 0x%08x ", r[31]);
		printf("\n\n"); 
	}

	delete	m_fpga;
}

