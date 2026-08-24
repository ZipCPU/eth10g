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
// Copyright (C) 2025-2026, Gisselquist Technology, LLC
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
#include <inttypes.h>

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

#ifndef	R_ROUTER
#define	NO_STATREGS
#else
  #ifndef	R_NETSTAT
  #define	NO_STATREGS
  #endif
#endif

#define	LLD	PRId64

int main(int argc, char **argv) {
#ifdef	NO_STATREGS
	printf("No stat registers defined\n");
#else
	int	skp=0;
	const char *host = FPGAHOST;
	int	port=FPGAPORT;
	unsigned	net_clk[6], net_reset, net_lock, net_dbg;

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

	unsigned	ubuf[64], sbuf[128], cbuf[32];
	typedef union	WIDE_U {
		uint64_t	l;
		struct	{
			uint32_t lo, hi;
		} u;
	} WIDE;

	WIDE		tm; //rx, tx;

	// R_NETRESET
	// {{{
	net_reset = m_fpga->readio(R_NETRESET);
	// }}}
	// Get the network clock status
	// {{{
	// R_RXNETCK[0:3]
	// R_TXNETCLK
	// R_REFNETCLK
	// unsigned	net_clk[6];
	m_fpga->readi(R_RXNETCK0, sizeof(net_clk)/sizeof(unsigned), net_clk);
	// }}}
	// R_NETLOCK
	// {{{
	net_lock = m_fpga->readio(R_NETLOCK);
	// }}}

	m_fpga->readi(R_ROUTER,  sizeof(ubuf)/sizeof(unsigned), ubuf);
	// R_NETSTAT
	m_fpga->readi(R_NETSTAT, sizeof(sbuf)/sizeof(unsigned), sbuf);
	// R_NETDBG
#ifdef	R_NETDBG
	net_dbg = m_fpga->readio(R_NETDBG);
#else
	net_dbg = 0;
#endif

	// R_CPUNET
	// {{{
	m_fpga->readi(R_CPUNET, sizeof(cbuf)/sizeof(unsigned), cbuf);
	// }}}

	// RESET info
	// {{{
	if (net_reset == 0)
		printf("NET-RESET:      All nodes running\n");
	else {
		printf("NET-RESET:      ");
		for(int n=0; n<5; n++) {
			if (net_reset & (1<<n))
				printf("Link-%d in reset  ", n);
		} printf("\n");
	}
	// }}}

	// Clock info
	// {{{
	m_fpga->readi(R_RXNETCK0, sizeof(net_clk)/sizeof(unsigned), net_clk);
	if (net_clk[5] == 0)
		printf("CLK NET.REF  :  ERROR.  No clock present\n");
	else {
		printf("CLK NET.REF  :  %10.6f MHz\n", net_clk[5] / 1e6);
		if (net_clk[4] == 0) {
			printf("CLK NET.TX   :  ERROR.  No clock present\n");
		} else {
			printf("CLK NET.TX   :  %10.6f MHz\n", net_clk[4] / 1e6);

			for(int n=0; n<4; n++) {
				if (net_clk[n] == 0) {
					printf("CLK NET.RX[%1d]:  ERROR.  No clock present\n", n);
				} else {
					printf("CLK NET.RX[%1d]:  %10.6f MHz\n", n, net_clk[n] / 1e6);
				}
			}
		}
	}
	// }}}

	printf("Net Lock   :    0x%08x\n", net_lock);

	// Lock info
	// {{{
	if (0 == (net_lock & 0x010))
		printf("   PHY PLLs:    No lock\n");
	else if (0x0f == (net_lock & 0x0f)) {
		printf("   PHY PLLs:    All four channels locked\n");
	} else {
		printf("   PHY PLLs:    ");
		for(int n=0; n<4; n++) {
			if (net_lock & (1<<n))
				printf("#%d Locked ", n);
			else
				printf("#%d NO LOCK", n);
			if (n < 3)
				printf(",  ");
		} printf("\n");
	}

	if (0 == (net_lock & 0x0f00))
		printf("    LOS    :    All signals present\n");
	else {
		printf("    LOS    :    ");

		for(int n=0; n<4; n++) {
			if (net_lock & (0x100 << n)) {
				printf("%d NO SIGNAL", n);
			} else
				printf("%d Signal Up", n);
			if (n < 3)
				printf(", ");
		} printf("\n");
	}
	// }}}

	// NetDBG info
	// {{{
	printf("Net Debug  :    0x%08x\n", net_dbg);
	printf("  Debug    :      Ch #%d\n", net_dbg & 0x3);
	printf("  LinkUp   :    %d-%d-%d-%d\n",
			(net_dbg & 0x0800) ? 1:0, (net_dbg & 0x0400) ? 1:0,
			(net_dbg & 0x0200) ? 1:0, (net_dbg & 0x0100) ? 1:0);
	printf("  Activity :    %d-%d-%d-%d\n",
			(net_dbg & 0x080000) ? 1:0, (net_dbg & 0x040000) ? 1:0,
			(net_dbg & 0x020000) ? 1:0, (net_dbg & 0x010000) ? 1:0);
	// }}}

	for(int n=0; n<4; n++) {	// Router stats
		// {{{
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
		tm.u.lo = sbuf[32*n + 0]; tm.u.hi = sbuf[32*n + 1]; // rx.l=tm.l;
		printf("  RX   Packets: %13" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 2]; tm.u.hi = sbuf[32*n + 3];
		printf("  RX   Bytes: %15" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 4]; tm.u.hi = sbuf[32*n + 5];
		printf("  RX   Aborts:     %10" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		// }}}

		// CRC
		// {{{
		tm.u.lo = sbuf[32*n + 6]; tm.u.hi = sbuf[32*n + 7];
		printf("  CRC  Packets: %13" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 8]; tm.u.hi = sbuf[32*n + 9];
		printf("  CRC  Bytes: %15" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 10]; tm.u.hi = sbuf[32*n + 11];
		printf("  CRC  Aborts:     %10" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		// }}}

		// TX
		// {{{
		tm.u.lo = sbuf[32*n + 12]; tm.u.hi = sbuf[32*n + 13];
		printf("  TX   Packets: %13" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 14]; tm.u.hi = sbuf[32*n + 15];
		printf("  TX   Bytes: %15" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 16]; tm.u.hi = sbuf[32*n + 17];
		printf("  TX   Aborts:     %10" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		// }}}

		// TX-Gate
		// {{{
		tm.u.lo = sbuf[32*n + 18]; tm.u.hi = sbuf[32*n + 19]; //tx.l=tm.l;
		printf("  Gate Packets: %13" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 20]; tm.u.hi = sbuf[32*n + 21];
		printf("  Gate Bytes: %15" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		tm.u.lo = sbuf[32*n + 22]; tm.u.hi = sbuf[32*n + 23];
		printf("  Gate Aborts:     %10" LLD " (%08x:%08x)\n", tm.l, tm.u.hi, tm.u.lo);
		// }}}

		printf("  FIFO TX Packets: %10d (0x%08x)\n", vpkt[0], vpkt[0]);
		printf("  FIFO TX Bytes:   %10d (0x%08x)\n", vpkt[1], vpkt[1]);
		printf("  FIFO Packets:    %10d (0x%08x)\n", vpkt[2], vpkt[2]);
		printf("  FIFO Bytes:      %10d (0x%08x)\n", vpkt[3], vpkt[3]);
		// }}}
	}

	printf("ROUTE-NEVER:       %02x,%02x,%02x,%02x|%02x -- 0x%08x\n",
			(ubuf[58] >>  0) & 0x3f,
			(ubuf[58] >>  6) & 0x3f,
			(ubuf[58] >> 12) & 0x3f,
			(ubuf[58] >> 18) & 0x3f,
			(ubuf[58] >> 24) & 0x3f,
			ubuf[58]);
		for(int n=0; n<5; n++) {
			// {{{
			// 58 = 0x3a
			unsigned	unvr = (ubuf[58] >> (n*6)) & 0x03f;

			if (unvr == (1u<<n))
				continue;

			if (4 == n)
				printf("\tCPU TX  *NEVER* routes to channels: ");
			else
				printf("\tChan #%d *NEVER* routes to channels: ", n);
			for(int u=0; u<5; u++) {
				if (unvr & (1 << u)) {
					if (4 == u)
						printf("CPU");
					else
						printf("%1d ", u);
				}
			} printf("\n");
			// }}}
		}
	printf("ROUTE-ALWAYS:      %02x,%02x,%02x,%02x|%02x -- 0x%08x\n",
			(ubuf[59] >>  0) & 0x3f,
			(ubuf[59] >>  6) & 0x3f,
			(ubuf[59] >> 12) & 0x3f,
			(ubuf[59] >> 18) & 0x3f,
			(ubuf[59] >> 24) & 0x3f,
			ubuf[59]);
		for(int n=0; n<5; n++) {
			// {{{
			// 59 = 0x3b
			unsigned	unow = (ubuf[59] >> (n*6)) & 0x03f;

			if (unow == 0)
				continue;

			if (4 == n)
				printf("\tCPU TX  *ALWAYS* routes to channels: ");
			else
				printf("\tChan #%d *ALWAYS* routes to channels: ", n);
			for(int u=0; u<5; u++) {
				if (unow & (1 << u)) {
					if (4 == u)
						printf("CPU");
					else
						printf("%1d ", u);
				}
			} printf("\n");
			// }}}
		}
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

	// CPU Net VFIFO
	// {{{
	{
		printf("CPU-Net ---\n");
		printf("  CPU MAC:                 %02x:%02x:%02x:%02x:%02x:%02x\n",
			(cbuf[1] >> 8)&0x0ff,  (cbuf[1] & 0x0ff),
			(cbuf[2] >> 24)&0x0ff, (cbuf[2] >> 16) & 0x0ff,
			(cbuf[2] >>  8)&0x0ff, (cbuf[2] & 0x0ff));

		printf("  CPU IPv4 Address:        %d.%d.%d.%d\n",
			(cbuf[3] >> 24)&0x0ff, (cbuf[3] >> 16) & 0x0ff,
			(cbuf[3] >>  8)&0x0ff, (cbuf[3] & 0x0ff));

		printf("  CPU RX Packets:             %8d\n", cbuf[9]);
		printf("  CPU RX Pkts dropd:          %8d\n", cbuf[8]);
		printf("  CPU TX Packets:             %8d\n", cbuf[10]);
		if (0 == cbuf[16] || 0 == cbuf[17]) {
			printf("  CPU VFIFO TX:             (Not configured / inactive)\n");
		} else {
			printf("  CPU VFIFO TX MEM:         0x%08x\n", cbuf[16]);
			printf("  CPU VFIFO TX LN:          0x%08x\n", cbuf[17]);
			printf("  CPU VFIFO TX Active:        %8d bytes\n",
				(cbuf[19] - cbuf[18]) & (cbuf[17]-1));
		}
		if (0 == cbuf[20] || 0 == cbuf[21]) {
			printf("  CPU VFIFO RX:             (Not configured / inactive)\n");
		} else {
			printf("  CPU VFIFO RX MEM:         0x%08x\n", cbuf[20]);
			printf("  CPU VFIFO RX LN:          0x%08x\n", cbuf[21]);
			printf("  CPU VFIFO RX Active:        %8d bytes\n",
				(cbuf[23] - cbuf[22]) & (cbuf[21]-1));
		}

		printf("  CPU VFIFO RX DBG:         0x%08x\n", cbuf[24]);
		printf("  CPU VFIFO TX DBG:         0x%08x\n", cbuf[25]);
	}
	// }}}


	delete	m_fpga;
#endif
}

