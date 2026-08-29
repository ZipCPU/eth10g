////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/swloader.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	The ZipCPU half of SWLOAD.  Waits for a descriptor in SDRAM,
//		verifies each region's checksum, and writes it to flash.
//
//	Writing flash from the host takes hours because every byte crosses the
//	debug bus.  Here the host stages the payload in SDRAM once and this
//	loader does the flash writes at hardware speed.
//
//	The other half is sw/host/swload.cpp; the constants they share come
//	from autodata/swload.txt.
//
// Creator:	Sukru Uzun.
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
//
// }}}
#include "zipcpu.h"
#include "txfns.h"
#include "flashdev.h"
#include "board.h"
#include "oledfont.h"
#include "oledfb.h"

extern unsigned _sdram_words[] __asm__("_sdram");
// unsigned *_sdram_words = (unsigned *)_sdram;

#define SWLOAD_HEARTBEAT_ADDR  ((unsigned)_sdram_words)
#define SWLOAD_DESCRIPTOR_ADDR ((unsigned)_sdram_words + 4)

// #define SWLOAD_MAGIC       0x53574c44  // 'SWLD'
// #define SWLOAD_CMD_GO      0x00000001
// #define SWLOAD_MAX_REGIONS 8

// r_chechsum: Virtual FIFO can write to our staging area (SDRAM),
// We need to make sure image is not corrupted.
typedef struct {
	unsigned r_src;
	unsigned r_dst;
	unsigned r_len;       // byte
	unsigned r_checksum;
} SWLOAD_REGION;

typedef struct {
	volatile unsigned d_command;    // host writes, CPU acks or fails or etc.
	// volatile unsigned d_heartbeat;  // CPU alive ?
	unsigned d_magic;   // "SWLD"
	unsigned d_nregions;
	SWLOAD_REGION d_region[SWLOAD_MAX_REGIONS];
} SWLOAD_DESC;

static volatile unsigned *const heartbeatp = (volatile unsigned *)(SWLOAD_HEARTBEAT_ADDR);
static SWLOAD_DESC *const descp = (SWLOAD_DESC *)SWLOAD_DESCRIPTOR_ADDR;

int main(void) {
	int ok = 1;

	txstr("----------------------------------------\n");
	txstr("--          ZipCPU S/W Loader         --\n");
	txstr("----------------------------------------\n");
#ifndef	NO_OLED
	_i2c->ic_clkcount = 500;
	init_tall_glyfs();
	init_short_glyfs();
	oled_hwsetup();
	fb_font = tallfontp;
#endif
	// txstr("Descriptor at: "); txhex((unsigned)descp); txstr("\n");

	txstr("SWLOAD: Waiting for command ...\n");
	while (descp->d_command != SWLOAD_CMD_GO)
		CLEAR_CACHE;

	txstr("SWLOAD: Command received\n");
	// txstr("\ttmagic    = "); txhex(descp->d_magic); txstr("\n");
	txstr("\ttnregions = "); txhex(descp->d_nregions); txstr("\n");

	descp->d_command = SWLOAD_STAT_WAIT;    // begin to work

	for (unsigned k = 0; k < descp->d_nregions; k++) {
        	CLEAR_CACHE;
        	*heartbeatp = *heartbeatp + 1;

        	txstr("Region "); txhex(k);
        	txstr(": "); txhex(descp->d_region[k].r_len);
        	txstr(" bytes -> "); txhex(descp->d_region[k].r_dst);
        	txstr(" from "); txhex(descp->d_region[k].r_src); txstr("\n");

        	// Verify the staged copy before we burn it into flash. A bad
		// transfer over the debug bus is recoverable here, once
		// written it is not.
        	const unsigned *p = (const unsigned *)descp->d_region[k].r_src;
        	unsigned nw = (descp->d_region[k].r_len + 3) / 4;
        	unsigned sum = 0;

		for(unsigned i=0; i<nw; i++)
			sum += p[i];

		if (sum != descp->d_region[k].r_checksum) {
			txstr("SWLOAD: CHECKSUM FAIL on region "); txhex(k);
			txstr("  got "); txhex(sum);
			txstr("  want "); txhex(descp->d_region[k].r_checksum);
			txstr("\n");
			ok = 0;
			break;
		}

		if (!fl_write(descp->d_region[k].r_dst,descp->d_region[k].r_len,
				(const char *)descp->d_region[k].r_src, 1)) {
			txstr("SWLOAD: FAILED on region ");
			txhex(k); txstr("\n");
			ok = 0;
			break;
		}
	}

	txstr(ok ? "SWLOAD: Complete\n" : "SWLOAD: FAILED!\n");
	descp->d_command = ok ? SWLOAD_STAT_DONE : SWLOAD_STAT_FAIL;

	zip_halt();
}
