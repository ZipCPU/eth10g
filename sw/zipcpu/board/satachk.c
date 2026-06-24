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
#include <stdlib.h>
#include "zipcpu.h"
#include "zipsys.h"
#include "board.h"
// }}}

const	unsigned	FIS_REG_H2D	= 0x027,
			FIS_REG_D2H	= 0x034,
			FIS_DMA_ACTIVATE = 0x039,
			FIS_DMA_SETUP	= 0x041,
			FIS_DATA_FIS	= 0x046,
			FIS_BIST_ACTIVATE = 0x058,
			FIS_PIO_SETUP	= 0x05f,
			FIS_SETBITS	= 0x0a1;
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

void	wait_second(void) {
	_zip->z_tma = 100000000;
	while(_zip->z_tma > 0)
		;
}

void	wait_msec(unsigned count) {
	for(; count > 0; count--) {
		_zip->z_tma = 100000;
		while(_zip->z_tma > 0)
			;
	}
}

void	wait_int(unsigned int_mask) {
//	_zip->z_pic = DALLPIC|mask;
//	_zip->z_pic = EINT|mask;
//	zip_rtu();
//	_zip->z_pic = DINT|mask;
	unsigned	pic = _zip->z_pic;
	unsigned	en = (0x8000 | int_mask) << 16;

	if (en != ((pic & en) & 0xffff0000)) {
		unsigned	dis = (pic & (~en)) & 0x7fff0000;

		// Disable any interrupts we're not interested in
		if (0 != dis)
			_zip->z_pic = dis;

		// Enable the ones we are interested in
		_zip->z_pic = en | 0x8000;
	} pic = _zip->z_pic;
	if (0 == (pic & int_mask))
		zip_idle();
}

void	dump_drp(void) {
	for(int k=0x30; k<0x48; k+=8) {
		printf("DLL %04x: ", k);
		for(int s=0; s<8; s++) {
			printf(" 0x%04x", _satadrp->d_pll[k+s] & 0x0ffff);
		} printf("\n");
	}

	for(int k=0; k<0xae; k+=8) {
		printf("GTX %04x: ", k);
		for(int s=0; s<8; s++) {
			printf(" 0x%04x", _satadrp->d_gtx[k+s] & 0x0ffff);
		} printf("\n");
	}
	// printf("GTX %04x: ", 0x150, _satadrp->d_gtx[0x150]);
	printf("GTX %04x: ", 0x15e, _satadrp->d_gtx[0x15e]);
}

void	dump_regs(void) {
	unsigned	cmd, lhi, llo, cnt, phy;

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
	printf("\tPHY     : 0x%08x\n", (phy = _sata->s_phy));
	printf("\t  State :          %1x ", (phy >> 4) & 0x0f);
	switch((phy >> 4) & 0x0f) {
	case 0: printf("IDLE\n"); break;
	case 1: printf("COMMAND\n"); break;
	case 2: printf("PIO-IN-SETUP\n"); break;
	case 3: printf("PIO-RXDATA\n"); break;
	case 4: printf("PIO-OUT-SETUP\n"); break;
	case 5: printf("PIO-TXDATA\n"); break;
	case 6: printf("DMA-IN\n"); break;
	case 7: printf("DMA-IN (FINAL)\n"); break;
	case 8: printf("DMA-OUT-SETUP\n"); break;
	case 9: printf("DMA TXDATA\n"); break;
	case 10: printf("WAIT-REG\n"); break;
	default: printf("(Unknown state)\n");
	}
	printf("\t  Faild :        %s\n", (phy & 8) ? "ERR":"");
	printf("\t  Droppd:        %s\n", (phy & 4) ? "DRP":"");
	printf("\t   Hold :        %s\n", (phy & 2) ? "HLD":"");
	printf("\t   Reset:        %s\n", (phy & 1) ? "RST":"");
	printf("\tDMA     : 0x%08x\n", (unsigned)_sata->s_dma);
}

void	identify_device(void) {
	// COMMAND = 8'hec
	// COUNT (unused)
	// FEATUERE (unused)
	// LBA (N/A)
	// PIO Data-In
	char	*dma_buffer;
	dma_buffer = malloc(512);	// What should this be?
	_sata->s_dma = (void *)dma_buffer;
	_sata->s_cmd = 0x0ec0027;

	dump_regs();
	wait_second();
	dump_regs();
	wait_second();
	dump_regs();
}

int	main(int argc, char **argv) {
	// Announce our presence
	// {{{
	printf("\n\n"
		"+-----------------------------------------+\n"
		"|        SATA (Gen 1) Test Program        |\n"
		"+-----------------------------------------+\n");
	// }}}

	// Clear any SATASCOPEs before doing anything
	// {{{
#ifdef	_BOARD_HAS_SATAPSCOPE
	_satapscope->s_ctrl = 0;	// WBSCOPE_DISABLE
#endif
#ifdef	_BOARD_HAS_SATARSCOPE
	_satarscope->s_ctrl = 0;	// WBSCOPE_DISABLE
#endif
#ifdef	_BOARD_HAS_SATALSCOPE
	_satalscope->s_ctrl = 0;	// WBSCOPE_DISABLE
#endif
#ifdef	_BOARD_HAS_SATATSCOPE
	_satatscope->s_ctrl = 0;	// WBSCOPE_DISABLE
#endif
	// }}}

	// Check if the link is up
	//	If not, reset, wait 1ms, clear reset, wait 1s
	// If not, generate and produce debug data
	// {{{
	dump_drp();

	dump_regs();
	// }}}

	// Get the device's status
	// Read out the device's size
}
