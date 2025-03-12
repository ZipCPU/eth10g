////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/routestat.cpp
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
// Copyright (C) 2025, Gisselquist Technology, LLC
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
#include <stdint.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "regdefs.h"
#include "port.h"
#include "ttybus.h"
// #include "hexbus.h"

typedef	TTYBUS FPGA;

FPGA	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

void	usage(void) {
	printf("USAGE: routestat\n");
}

int main(int argc, char **argv) {
	int	skp=0;
	const char *host = FPGAHOST;
	int	port=FPGAPORT;

	skp=1;
	for(int argn=0; argn<argc-skp; argn++) {
		if (argv[argn+skp][0] == '-') {
			if (argv[argn+skp][1] == 'n') {
				if (argn+skp+1 >= argc) {
					fprintf(stderr, "ERR: No network host given\n");
					exit(EXIT_SUCCESS);
				}
				host = argv[argn+skp+1];
				skp++; argn--;
			} else if (argv[argn+skp][1] == 'p') {
				if (argn+skp+1 >= argc) {
					fprintf(stderr, "ERR: No network port # given\n");
					exit(EXIT_SUCCESS);
				}
				port = strtoul(argv[argn+skp+1], NULL, 0);
				skp++; argn--;
			} else {
				usage();
				exit(EXIT_SUCCESS);
			}
			skp++; argn--;
		} else
			argv[argn] = argv[argn+skp];
	} argc -= skp;

	m_fpga = new FPGA(new NETCOMMS(host, port));

	unsigned	ubuf[64], sbuf[128];
	typedef union	WIDE_U {
		uint64_t	l;
		struct	{
			uint32_t lo, hi;
		} u;
	} WIDE;

	WIDE		tm, rx, tx;

	m_fpga->readi(R_ROUTER,  sizeof(ubuf)/sizeof(unsigned), ubuf);
	m_fpga->readi(R_NETSTAT, sizeof(sbuf)/sizeof(unsigned), sbuf);

	for(int n=0; n<4; n++) {
		unsigned	*macp = &ubuf[32 + 4*n], *vpkt = &ubuf[16+ 4*n];
		printf("Route #%d\n", n);
		printf("  Last RX MAC:     %02x:%02x:%02x:%02x:%02x:%02x\n",
			(macp[0] >> 8)&0x0ff, (macp[0] & 0x0ff),
			(macp[1] >> 24)&0x0ff, (macp[1] >> 16) & 0x0ff,
			(macp[1] >>  8)&0x0ff, (macp[1] & 0x0ff));

		printf("  Last TX MAC:     %02x:%02x:%02x:%02x:%02x:%02x\n",
			(macp[2] >> 8)&0x0ff, (macp[2] & 0x0ff),
			(macp[3] >> 24)&0x0ff, (macp[3] >> 16) & 0x0ff,
			(macp[3] >>  8)&0x0ff, (macp[3] & 0x0ff));

		// RX
		// {{{
		tm.u.lo = sbuf[32*n + 0]; tm.u.hi = sbuf[32*n + 1]; rx.l=tm.l;
		printf("  RX   Packets: %13lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 2]; tm.u.hi = sbuf[32*n + 3];
		printf("  RX   Bytes: %15lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 4]; tm.u.hi = sbuf[32*n + 5];
		printf("  RX   Aborts:     %10lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		// }}}

		// CRC
		// {{{
		tm.u.lo = sbuf[32*n + 6]; tm.u.hi = sbuf[32*n + 7];
		printf("  CRC  Packets: %13lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 8]; tm.u.hi = sbuf[32*n + 9];
		printf("  CRC  Bytes: %15lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 10]; tm.u.hi = sbuf[32*n + 11];
		printf("  CRC  Aborts:     %10lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		// }}}

		// TX
		// {{{
		tm.u.lo = sbuf[32*n + 12]; tm.u.hi = sbuf[32*n + 13];
		printf("  TX   Packets: %13lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 14]; tm.u.hi = sbuf[32*n + 15];
		printf("  TX   Bytes: %15lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 16]; tm.u.hi = sbuf[32*n + 17];
		printf("  TX   Aborts:     %10lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		// }}}

		// TX-Gate
		// {{{
		tm.u.lo = sbuf[32*n + 18]; tm.u.hi = sbuf[32*n + 19]; tx.l=tm.l;
		printf("  Gate Packets: %13lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 20]; tm.u.hi = sbuf[32*n + 21];
		printf("  Gate Bytes: %15lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 22]; tm.u.hi = sbuf[32*n + 23];
		printf("  Gate Aborts:     %10lld (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		// }}}

		printf("  FIFO TX Packets: %10d (0x%08x)\n", vpkt[0], vpkt[0]);
		printf("  FIFO TX Bytes:   %10d (0x%08x)\n", vpkt[1], vpkt[1]);
		printf("  FIFO Packets:    %10d (0x%08x)\n", vpkt[2], vpkt[2]);
		printf("  FIFO Bytes:      %10d (0x%08x)\n", vpkt[3], vpkt[3]);
	}

	printf("ROUTE-NEVER:       %02x,%02x,%02x,%02x|%02x -- 0x%08x\n",
			(ubuf[58] >>  0) & 0x3f,
			(ubuf[58] >>  6) & 0x3f,
			(ubuf[58] >> 12) & 0x3f,
			(ubuf[58] >> 18) & 0x3f,
			(ubuf[58] >> 24) & 0x3f,
			ubuf[58]);
	printf("ROUTE-ALWAYS:      %02x,%02x,%02x,%02x|%02x -- 0x%08x\n",
			(ubuf[59] >>  0) & 0x3f,
			(ubuf[59] >>  6) & 0x3f,
			(ubuf[59] >> 12) & 0x3f,
			(ubuf[59] >> 18) & 0x3f,
			(ubuf[59] >> 24) & 0x3f,
			ubuf[59]);
	/*
	for(int k=0; k<64; k++) {
		printf("%08x ", ubuf[k]);
		if (7 == (k & 7))
			printf("\n");

		if (15 == k)
			printf("\n");
		else if (31 == k)
			printf("\n");
	}

	for(int k=0; k<128; k++) {
		printf("%08x ", sbuf[k]);
		if (7 == (k & 7))
			printf("\n");
	}
	*/

	delete	m_fpga;
}

