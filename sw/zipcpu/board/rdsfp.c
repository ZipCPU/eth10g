////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rdsfp.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Reads the SFP+ I2C data from all four of the I2C devices in the
//		system.  (Based on the instructions given in sfp.c ...)
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
// }}}

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include "zipcpu.h"
#include "zipsys.h"
#include "board.h"

#include "sfp.c"

int main(int argc, char **argv) {
#ifndef	_BOARD_HAS_I2CCPU
	printf("ERR: This software requires the I2C controller\n");
#else
#ifndef	_BOARD_HAS_I2CDMA
	printf("ERR: This software requires the I2C DMA\n");
#else

	char	*cfgmem;
	unsigned	c = 0, ln = 0;
	printf("\n\n"
		"+-----------------------------------------+\n"
		"|  SFP+ I2C Configuration Reader / tester |\n"
		"+-----------------------------------------+\n");

#ifdef	_BOARD_HAS_I2CSCOPE
	_i2cscope->s_ctrl = 0x04000000u;

	// Now wait for the scope to prime
	while(0 == (_i2cscope->s_ctrl & 0x10000000u))
		;
	printf("I2C Scope   = %08x\n", _i2cscope->s_ctrl);
#endif

	// Make sure the I2C controller is halted from whatever else
	// it might've been doing.
	// {{{
	_i2c->ic_control = 0x0780000;
	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0080000));

	printf("I2C Control = %08x\n", c);
	// }}}

	// Configure the I2C DMA to collect the data we need
	// {{{
	printf("Configuring the I2C DMA\n");

	// We'll put the configuration memory we read into an area of memory
	// pointed to by cfgmem
	cfgmem = (char *)malloc(1024);
	_i2cdma->id_base   = (unsigned)cfgmem;
	_i2cdma->id_memlen = 1024;

	// The DMA starts automatically when given a valid memory region.
	//   Now, whenever the I2C controller reads a byte of data, it will
	//   get automatically written to our memory region.
	// }}}

	// Request the data from the I2C controller
	// {{{
	printf("Commanding read SFP+ data areas ...\n");

	_i2c->ic_address = (unsigned)i2casm;
#ifdef	_BOARD_HAS_I2CSCOPE
	_zip->z_tma = 0x00100000;
	while(_zip->z_tma != 0);
	_i2cscope->s_ctrl = 0x8c000000u;
#endif
	// }}}

	// Wait for the controller to complete
	// {{{
	do {
		c = _i2c->ic_control;
	} while(0 == (c & 0x0780000)); // While not halted and not aborted

	if (0 == (c & 0x080000)) {
		// We aborted.  Now halt.  Hard halt.
		_i2c->ic_control = 0x0080000;
	}
	// }}}

	if (c & 0x080000) {
		// We successfully read everything.  Examine the results
		// {{{
		CLEAR_DCACHE;
		printf("SFP+ Info:\n"
			"-------------------\n");

		ln = _i2cdma->id_current - _i2cdma->id_base;
		for(int k=0; k+95<ln; k+=96) {
			printf("Device #%d\n", k/96);
			for(int j=k; j<k+95; j++) {
				char	ch = cfgmem[j];

				printf("%02x%s", ch & 0x0ff,((j&15)==15) ? "\n" :", ");
			} printf("%02x\n", cfgmem[k+95] & 0x0ff);
		}

		for(int k=0; k+95<ln; k+=96) {
			char	*cfg = &cfgmem[k];
			printf("Decode device #%d\n", k/96);

			// Type of transceiver
			// {{{
			switch(cfg[0] & 0x0ff) {
			case 0: printf("[  0]: %02x Unknown or unspecified ID\n", cfg[0]); break;
			case 1: printf("[  0]: %02x GBIC\n", cfg[0]); break;
			case 2: printf("[  0]: %02x Module soldered to motherboard (ex: SFF)\n", cfg[0]); break;
			case 3: printf("[  0]: %02x SFP or SFP+\n", cfg[0]); break;
			default: 
				printf("[  0]: %02x RESERVED\n", cfg[0]); break;
			}
			// }}}

			// MOD_DEF
			// {{{
			if (cfg[1] >= 0x08)
				printf("%-16s: %02x (Unallocated)\n", "[  1] EXID",
					cfg[1]);
			else if (cfg[1] == 0x00)
				printf("%-16s: %02x GBIC definition is not "
					"specified or not compliant\n",
					"[  1] EXID", cfg[1]);
			else
				printf("%-16s: %s%d\n", "[  2] EXID",
					"GBIC is compliant with MOD_DEF ",
					cfg[1]);
			// }}}

			// Connector type
			// {{{
			if (cfg[2] >= 0x80)
				printf("%-16s: %02x (Vendor specific connector)\n", "[  2] CONN",
					cfg[1]);
			else if (cfg[2] >= 0x23)
				printf("%-16s: %02x (Unallocated connector)\n",
					"[  2] CONN", cfg[1]);
			else if (cfg[2] >= 0x0d && cfg[2] <= 0x1f)
				printf("%-16s: %02x (Unallocated)\n",
					"[  2] CONN", cfg[1]);
			else {
				printf("%-16s: %02x", "[  2] CONN", cfg[1]);
				switch(cfg[2]) {
				case 0: printf("(Unspecified connector)\n"); break;
				case 1: printf("SC\n"); break;
				case 2: printf("Fibre Channel Style 1 copper connector\n"); break;
				case 3: printf("Fibre Channel Style 2 copper connector\n"); break;
				case 4: printf("BNC/TNC\n"); break;
				case 5: printf("Fibre Channel coaxial headers\n"); break;
				case 6: printf("FiberJack\n"); break;
				case 7: printf("LC\n"); break;
				case 8: printf("MT-RJ\n"); break;
				case 9: printf("MU\n"); break;
				case 10: printf("SG\n"); break;
				case 11: printf("Optical pigtail\n"); break;
				case 12: printf("MPO Parallel Optic\n"); break;
				case 32: printf("HSSDC II\n"); break;
				case 33: printf("Copper pigtail\n"); break;
				case 34: printf("RJ45\n"); break;
				default: printf("(Other?)\n");
				}
			}
			// }}}

			// Encoding type
			// {{{
			printf("%-16s: %02x ",
					"[ 11] Encoding", cfg[11]);
			switch(cfg[11]) {
			case 0:	printf(" Unspecified\n"); break;
			case 1:	printf(" 8B/10B\n"); break;
			case 2:	printf(" 4B/5B\n"); break;
			case 3:	printf(" NRZ\n"); break;
			case 4:	printf(" Manchester\n"); break;
			case 5:	printf(" SONET Scrambled\n"); break;
			case 6:	printf(" 64B/66B\n"); break;
			default:	printf(" (Unallocated / reserved)\n");
			}
			// }}}

			// Nominal rate
			// {{{
			printf("%-16s: %02x - %5.1f Gb/s\n",
					"[ 12] NOM RATE", cfg[12],
					(double)((unsigned)cfg[12])/10.0);
			// }}}

			// Rate ID
			// {{{
			printf("%-16s: %02x ",
					"[ 13] Rate ID", cfg[13]);
			switch(cfg[13]) {
			case 0: printf("Unspecified\n"); break;
			case 1: printf("Defined for SFF-8079 (4/2/1G Rate_Select & AS0/AS1)\n"); break;
			case 2: printf("Defined for SFF-8431\n"); break;
			case 3: printf("Unspecified\n"); break;
			case 4: printf("Defined for SFF-8431 (8/4/2G Tx Rate_Select only)\n"); break;
			case 5: printf("Unspecified\n"); break;
			case 6: printf("Defined for SFF-8431 (8/4/2G Independent Rx & Tx Rate select)\n"); break;
			case 7: printf("Unspecified\n"); break;
			case 8: printf("Defined for FC-PI-5 (16/8/4G Rx Rate Select only)\n"); break;
			case 9: printf("Unspecified\n"); break;
			case 10: printf("Defined for FC-PI-5 (16/8/4G Independent Rx, Tx Rate Select)\n"); break;
			default:
				printf("(Reserved?)\n");
			}
			// }}}

			// Vendor name
			// {{{
			printf("%-16s: ", "[ 20] Vendor");
			for(int j=20; j<35; j++) {
				if (isgraph(cfg[j]))
					printf("%c", cfg[j]);
				else
					printf(".");
			} printf("\n");
			// }}}

			// Part number
			// {{{
			printf("%-16s: ", "[ 40] Part No.");
			for(int j=40; j<55; j++) {
				if (isgraph(cfg[j]))
					printf("%c", cfg[j]);
				else
					printf(".");
			} printf("\n");
			// }}}

			// Date code / Lot
			// {{{
			printf("%-16s: 20", "[84-91] Date cod");
			printf("%c", isgraph(cfg[84]) ? cfg[84] : '.');
			printf("%c", isgraph(cfg[85]) ? cfg[85] : '.');
			printf("%c", isgraph(cfg[86]) ? cfg[86] : '.');
			printf("%c", isgraph(cfg[87]) ? cfg[87] : '.');
			printf("%c", isgraph(cfg[88]) ? cfg[88] : '.');
			printf("%c", isgraph(cfg[89]) ? cfg[89] : '.');
			printf(", Lot %c", isgraph(cfg[90]) ? cfg[90] : '.');
			printf("%c\n", isgraph(cfg[91]) ? cfg[91] : '.');
			// }}}

			printf("%-16s: %02x\n", "[ 92] DiagMon", cfg[92]);
			printf("%-16s: %02x\n", "[ 93] Enhanced", cfg[93]);
		}
		// }}}
	}
	else
		printf("I2C opn aborted.  Is the memory plugged in?\n");
#endif	// _BOARD_HAS_I2CDMA
#endif	// _BOARD_HAS_I2CCPU
}

/*
+-----------------------------------------+
|  SFP+ I2C Configuration Reader / tester |
+-----------------------------------------+
I2C Scope   = 16a00000
I2C Control = 0008f0a3
Configuring the I2C DMA
Commanding read SFP+ data areas ...
SFP+ Info:
-------------------
Device #0
50, 00, f6, 00, 4b, 00, fb, 00, 90, 88, 71, 48, 88, b8, 79, 18
1f, 40, 03, e8, 1d, 4c, 05, dc, 27, 10, 03, 1a, 22, d0, 03, 7b
31, 2d, 00, 3f, 27, 10, 00, 46, 00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 3f, 80, 00, 00, 00, 00, 00, 00, 01, 00, 00, 00
01, 00, 00, 00, 01, 00, 00, 00, 01, 00, 00, 00, 00, 00, 00, 63
Device #1
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
Device #2
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff, ff
Device #3
50, 00, f6, 00, 4b, 00, fb, 00, 90, 88, 71, 48, 88, b8, 79, 18
1f, 40, 03, e8, 1d, 4c, 05, dc, 27, 10, 03, 1a, 22, d0, 03, 7b
31, 2d, 00, 3f, 27, 10, 00, 46, 00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 3f, 80, 00, 00, 00, 00, 00, 00, 01, 00, 00, 00
01, 00, 00, 00, 01, 00, 00, 00, 01, 00, 00, 00, 00, 00, 00, 63
*/
