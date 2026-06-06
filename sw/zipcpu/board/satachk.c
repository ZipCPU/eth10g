////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/satachk.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Bring up the SATA controller.  A separate piece of software will
//		constitute the actual driver.  The purpose of this S/W is
//	test and bringup only.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2026, Gisselquist Technology, LLC
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
#include <stdio.h>
#include <string.h>
#include "zipcpu.h"
#include "board.h"
// }}}

/*
typedef struct  SATADRP_S {
        unsigned        d_pll[512];
        unsigned        d_gtx[512];
} SATADRP;

typedef	struct	SATA_S {
	volatile unsigned	s_cmd, s_lbalo, s_lbahi, s_count;
	volatile unsigned	s_unused;
	volatile unsigned	s_phy;
	volatile unsigned	*s_dma;
	unsigned		s_unused_tail;
} SATA;

static volatile SATADRP *const _satadrp ...
static volatile SATA *const _sata = ((SATA *) ...
*/

#define	SETSCOPE	_satapscope = _satalscope = _satatscope = _satarscope = 0

void	dump_drp(void) {
	for(int k=0; k<1; k+=4) {
		printf("DLL %04x: ", k);
		for(int s=0; s<4; s++) {
			printf(" 0x%08x", _satadrp->d_pll[k+s]);
		} printf("\n");
	}

	for(int k=0; k<1; k+=4) {
		printf("GTX %04x: ", k);
		for(int s=0; s<4; s++) {
			printf(" 0x%08x", _satadrp->d_gtx[k+s]);
		} printf("\n");
	}
}

void	dump_regs(void) {
	unsigned	cmd, lhi, llo, cnt;

	printf("\tCMD     : 0x%08x\n", (cmd = _sata->s_cmd));
	printf("\t  FeatLO:   %02x\n", (cmd >> 24) & 0x0ff);
	printf("\t  Comand:     %02x\n", (cmd >> 16) & 0x0ff);
	printf("\t  INT   :       %2s\n", (cmd & 0x08000) ? "IN":"--");
	printf("\t  DMA-ER:       %2s\n", (cmd & 0x04000) ? "ER":"OK");
	printf("\t  Port  :       %02x\n", (cmd >>  8) & 0x0f);
	printf("\t  FISTyp:         %02x\n", cmd & 0x0ff);
	printf("\tLBA     : 0x%08x:%08x\n", (lhi=_sata->s_lbahi),
					(llo=_sata->s_lbalo));
	printf("\t  Device:            %02x\n",(llo >> 24) & 0x0ff);
	printf("\t  FeatHI:   %02x\n",(lhi >> 24) & 0x0ff);
	printf("\tCOUNT   : 0x%08x\n", (cnt = _sata->s_count));
	printf("\t  Contrl:   %02x\n",(cnt >> 24) & 0x0ff);
	printf("\t  ICC   :     %02x\n",(cnt >> 16) & 0x0ff);
	printf("\t  Count :       %04x\n", cnt & 0x0ffff );
	// printf("\tPHY     : 0x%08x\n", _sata->s_phy);
	printf("\tDMA     : 0x%08x\n", (unsigned)_sata->s_dma);
}

void	identify_device(void) {
	// COMMAND = 8'hec
	// COUNT (unused)
	// FEATUERE (unused)
	// LBA (N/A)
	// PIO Data-In
	// _sata->s_cmd = 0x0ec00XX;
}

int	main(int argc, char **argv) {

	printf("On startup:\n");
	dump_drp();

	dump_regs();
}
