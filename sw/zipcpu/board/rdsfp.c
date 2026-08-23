////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/rdsfp.c
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
	_i2cdma->id_memlen = 1024;	// > (96+128)*4 = 896

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
		ln = _i2cdma->id_current - _i2cdma->id_base;

		printf("SFP+ Info: (Ln = %3d)\n"
			"-------------------\n", ln);

		for(int k=0; (k < 4) && ((k+1)*(96+128) <= ln); k++) {
			char	*b = &cfgmem[k*(96+128)];

			printf("Device #%d\n", k);
			for(int j=0; j<95; j++) {
				char	ch = b[j];

				printf("%02x%s", ch & 0x0ff,((j&15)==15) ? "\n" :", ");
				if (7 == (j&15))
					printf(" ");
			} printf("%02x\n", b[95] & 0x0ff);

			printf("----\n");
			for(int j=96; j<96+127; j++) {
				char	ch = b[j];

				printf("%02x%s", ch & 0x0ff,((j&15)==15) ? "\n" :", ");
				if (7 == (j&15))
					printf(" ");
			} printf("%02x\n", b[96+127] & 0x0ff);
		}

		for(int k=0; k<4 && (k*(96+128)) < ln; k++) {
			char	*cfg = &cfgmem[k*(96+128)];
			printf("Decode device #%d\n", k);

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
				printf("%-16s: %s%d\n", "[  1] EXID",
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
				printf("%-16s: %02x ", "[  2] CONN", cfg[1]);
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

			// Diagnostic monitoring
			// {{{
			printf("%-16s: %02x\n", "[ 92] DiagMon", cfg[92]);
			if (cfg[92] & 0x080) {
				printf("%18s (Legacy implementations)\n","");
			} if (cfg[92] & 0x040) {
				printf("%18s Digital diagnostic monitoring\n","");
			} if (cfg[92] & 0x020) {
				printf("%18s Internally calibrated\n","");
			} if (cfg[92] & 0x010) {
				printf("%18s Externally calibrated\n","");
			} if (cfg[92] & 0x008) {
				printf("%18s Rcvd power measurement type: Avg Pwr\n","");
			} if (cfg[92] & 0x004) {
				printf("%18s Address change required\n","");
			} // Bits 1-0 are not allocated
			// }}}

			// Enhanced Options
			// {{{
			printf("%-16s: %02x\n", "[ 93] Enhanced", cfg[93]);
			if (cfg[93] & 0x080) {
				printf("%18s Optional alarm/warning flags\n","");
			} else if (cfg[93] & 0x040) {
				printf("%18s Optional soft TX Disable\n","");
			} else if (cfg[93] & 0x020) {
				printf("%18s Optional soft TX Fault\n","");
			} else if (cfg[93] & 0x010) {
				printf("%18s Optional soft RX LOS\n","");
			} else if (cfg[93] & 0x008) {
				printf("%18s Optional soft RATE_SELECT\n","");
			} else if (cfg[93] & 0x004) {
				printf("%18s Optional soft application select control\n","");
			} else if (cfg[93] & 0x002)
				printf("%18s Optional soft rate select per SFF-8431\n","");
			// }}}

			cfg += 96;

			// A2 Checksum
			{
				unsigned	sum = 0;
				for(int k=0; k<95; k++)
					sum += cfg[k];
				sum &= 0x0ff;
				if (sum != cfg[95]) {
					printf("A2 Checksum mismatch\n");
					continue;
				} else
					printf("A2 Checksum match\n");
			}

			// Temp
			printf("A2[ 96: 97] : 0x%02x:%02x (Digital Temp)\n", cfg[96], cfg[97]);
			printf("A2[ 98: 99] : 0x%02x:%02x (Internal Voltage)\n", cfg[98], cfg[99]);
			printf("A2[100:101] : 0x%02x:%02x (Bias Current)\n", cfg[100], cfg[101]);
			printf("A2[102:103] : 0x%02x:%02x (Tx Power)\n", cfg[102], cfg[103]);
			printf("A2[104:105] : 0x%02x:%02x (Rx Power)\n", cfg[104], cfg[105]);
			// A2 110
			// {{{
			printf("A2[    110] : 0x%02x\n", cfg[110]);
			if (cfg[110] & 0x080) {
				printf("%18s TX Disable\n", "");
			} if (cfg[110] & 0x040) {
				printf("%18s Soft TX Disable\n", "");
			} if (cfg[110] & 0x020) {
				printf("%18s RS(1) state\n", "");
			} if (cfg[110] & 0x010) {
				printf("%18s RS(2) state\n", "");
			} if (cfg[110] & 0x008) {
				printf("%18s Soft RS(2)\n", "");
			} if (cfg[110] & 0x004) {
				printf("%18s TX Fault State\n", "");
			} if (cfg[110] & 0x002) {
				printf("%18s RX LOS state\n", "");
			} if (cfg[110] & 0x001) {
				printf("%18s Data (not) Ready #\n", "");
			}
			// }}}
			printf("A2[    112] : 0x%02x (Alarms)\n", cfg[112]);
			printf("A2[    113] : 0x%02x (RX PWR Alarms)\n", cfg[113]);
			printf("A2[    116] : 0x%02x (Warnings)\n", cfg[116]);
			printf("A2[    117] : 0x%02x (RX PWR Warnings)\n", cfg[117]);
			printf("A2[    118] : 0x%02x (Extended control)\n", cfg[118]);
		}
		// }}}
	}
	else
		printf("I2C opn aborted.  Is the memory plugged in?\n");
#endif	// _BOARD_HAS_I2CDMA
#endif	// _BOARD_HAS_I2CCPU
}

/*
Script started on 2026-08-22 23:41:08+02:00 [TERM="screen.xterm-256color" TTY="/dev/pts/3" COLUMNS="80" LINES="24"]
Trying ::1...
Trying 127.0.0.1...
Connected to localhost.
Escape character is '^]'.


+-----------------------------------------+
|  SFP+ I2C Configuration Reader / tester |
+-----------------------------------------+
I2C Scope   = 16a00000
I2C Control = 0008f9a9
Configuring the I2C DMA
Commanding read SFP+ data areas ...
SFP+ Info: (Ln = 896)
-------------------
Device #0
03, 04, 21, 00, 00, 00, 00, 00,  04, 00, 00, 00, 67, 00, 00, 00
00, 00, 01, 00, 4f, 45, 4d, 20,  20, 20, 20, 20, 20, 20, 20, 20
20, 20, 20, 20, 00, 00, 40, 20,  53, 46, 50, 2d, 48, 31, 30, 47
42, 2d, 43, 55, 31, 4d, 20, 20,  30, 33, 20, 20, 01, 00, 00, e4
00, 00, 00, 00, 32, 36, 30, 32,  30, 34, 30, 35, 39, 31, 20, 20
20, 20, 20, 20, 32, 36, 30, 32,  30, 34, 20, 20, 00, 00, 00, 2b
----
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
Device #1
03, 04, 21, 00, 00, 00, 00, 00,  04, 00, 00, 00, 67, 00, 00, 00
00, 00, 01, 00, 4f, 45, 4d, 20,  20, 20, 20, 20, 20, 20, 20, 20
20, 20, 20, 20, 00, 00, 40, 20,  53, 46, 50, 2d, 48, 31, 30, 47
42, 2d, 43, 55, 31, 4d, 20, 20,  30, 33, 20, 20, 01, 00, 00, e4
00, 00, 00, 00, 32, 36, 30, 32,  30, 34, 30, 35, 39, 31, 20, 20
20, 20, 20, 20, 32, 36, 30, 32,  30, 34, 20, 20, 00, 00, 00, 2b
----
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
Device #2
03, 04, 07, 10, 00, 00, 00, 00,  00, 00, 00, 06, 67, 00, 00, 00
08, 03, 00, 1e, 4f, 45, 4d, 20,  20, 20, 20, 20, 20, 20, 20, 20
20, 20, 20, 20, 00, 00, 0a, 0d,  53, 46, 50, 2d, 31, 30, 47, 2d
53, 52, 20, 20, 20, 20, 20, 20,  20, 20, 20, 20, 03, 52, 00, 71
00, 1a, 0a, 58, 32, 30, 32, 33,  30, 35, 32, 39, 31, 36, 34, 32
20, 20, 20, 20, 32, 33, 30, 35,  32, 38, 20, 20, 68, f0, 03, 2f
----
5a, 00, f6, 00, 55, 00, fb, 00,  90, 88, 71, 48, 8c, a0, 75, 30
21, 34, 01, f4, 1b, 58, 03, e8,  18, a6, 04, eb, 15, f7, 06, 31
31, 2d, 00, 64, 27, 10, 00, 9e,  00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 00, 00, 00, 00,  00, 00, 00, 00, 00, 00, 00, 00
00, 00, 00, 00, 3f, 80, 00, 00,  00, 00, 00, 00, 01, 00, 00, 00
01, 00, 00, 00, 01, 00, 00, 00,  01, 00, 00, 00, 00, 00, 00, 34
22, d2, 81, 0f, 0f, 61, 12, 63,  11, 3d, 00, 00, 00, 00, 30, 00
00, 00, 00, 00, 00, 00, 00, 00,  ff, ff, ff, ff, ff, ff, ff, 01
Device #3
03, 04, 21, 00, 00, 00, 00, 00,  04, 00, 00, 00, 67, 00, 00, 00
00, 00, 02, 00, 49, 4e, 54, 45,  4c, 4c, 49, 4e, 45, 54, 20, 20
20, 20, 20, 20, 00, 00, 40, 20,  35, 30, 38, 34, 31, 34, 20, 20
20, 20, 20, 20, 20, 20, 20, 20,  30, 33, 20, 20, 01, 00, 00, c7
00, 00, 00, 00, 31, 30, 32, 30,  37, 35, 32, 32, 32, 37, 30, 30
30, 34, 35, 35, 32, 32, 30, 36,  32, 39, 20, 20, 00, 00, 00, 9f
----
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
ff, ff, ff, ff, ff, ff, ff, ff,  ff, ff, ff, ff, ff, ff, ff, ff
Decode device #0
[  0]: 03 SFP or SFP+
[  1] EXID      : GBIC is compliant with MOD_DEF 4
[  2] CONN      : 04 Copper pigtail
[ 11] Encoding  : 00  Unspecified
[ 12] NOM RATE  : 67 -  10.3 Gb/s
[ 13] Rate ID   : 00 Unspecified
[ 20] Vendor    : OEM............
[ 40] Part No.  : SFP-H10GB-CU1M.
[84-91] Date cod: 20260204, Lot ..
[ 92] DiagMon   : 00
[ 93] Enhanced  : 00
A2 Checksum mismatch (sum=a1 != ff, dbg=ff-ff-ff-ff)

Decode device #1
[  0]: 03 SFP or SFP+
[  1] EXID      : GBIC is compliant with MOD_DEF 4
[  2] CONN      : 04 Copper pigtail
[ 11] Encoding  : 00  Unspecified
[ 12] NOM RATE  : 67 -  10.3 Gb/s
[ 13] Rate ID   : 00 Unspecified
[ 20] Vendor    : OEM............
[ 40] Part No.  : SFP-H10GB-CU1M.
[84-91] Date cod: 20260204, Lot ..
[ 92] DiagMon   : 00
[ 93] Enhanced  : 00
A2 Checksum mismatch (sum=a1 != ff, dbg=ff-ff-ff-ff)

Decode device #2
[  0]: 03 SFP or SFP+
[  1] EXID      : GBIC is compliant with MOD_DEF 4
[  2] CONN      : 04 LC
[ 11] Encoding  : 06  64B/66B
[ 12] NOM RATE  : 67 -  10.3 Gb/s
[ 13] Rate ID   : 00 Unspecified
[ 20] Vendor    : OEM............
[ 40] Part No.  : SFP-10G-SR.....
[84-91] Date cod: 20230528, Lot ..
[ 92] DiagMon   : 68
                   Digital diagnostic monitoring
                   Internally calibrated
                   Rcvd power measurement type: Avg Pwr
[ 93] Enhanced  : f0
                   Optional alarm/warning flags
A2 Checksum match

A2[ 96: 97] : 22:d2 (Digital Temp)
A2[ 98: 99] : 81:0f (Internal Voltage)
A2[100:101] : 0f:61 (Bias Current)
A2[102:103] : 12:63 (Tx Power)
A2[104:105] : 11:3d (Rx Power)
A2[    110] : 30
                   RS(1) state
                   RS(2) state
Decode device #3
[  0]: 03 SFP or SFP+
[  1] EXID      : GBIC is compliant with MOD_DEF 4
[  2] CONN      : 04 Copper pigtail
[ 11] Encoding  : 00  Unspecified
[ 12] NOM RATE  : 67 -  10.3 Gb/s
[ 13] Rate ID   : 00 Unspecified
[ 20] Vendor    : INTELLINET.....
[ 40] Part No.  : 508414.........
[84-91] Date cod: 20220629, Lot ..
[ 92] DiagMon   : 00
[ 93] Enhanced  : 00
A2 Checksum mismatch (sum=a1 != ff, dbg=ff-ff-ff-ff)
*/
