////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/clkcheck.c
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
#include "board.h"
#include "zipsys.h"
#include "zipcpu.h"

#include "si.c"

#ifdef	_BOARD_HAS_REFCLKCOUNTER
#define	VALID_CLKCHECK
#elif	defined(_BOARD_HAS_SICLKCOUNTER)
#define	VALID_CLKCHECK
#elif	defined(_BOARD_HAS_NETCLK)
#define	VALID_CLKCHECK
#elif	defined(_BOARD_HAS_VIDPIPE)
#define	VALID_CLKCHECK
#endif

void	clkreport(const char *nm, const unsigned counts) {
	// {{{
	if (counts > 1000000)
		printf("%-20s: %10.6f MHz\n", nm, (double)counts / 1e6);
	else if (counts > 1000)
		printf("%-20s:    %7.3f kHz\n", nm, (double)counts / 1e3);
	else // if (counts > 0)
		printf("%-20s:       %3d  Hz\n", nm, counts);
}
// }}}

void	setup_siclk(void) {
	// {{{
	volatile char		readmem[16];
	volatile unsigned	c;
	int			alrm;

	(*_sirefclk) = 0x20000000;	// 100MHz
	(*_gpio) = GPIO_SET(GPIO_SIRESET);

	// Make sure the I2C controller is clear
	// {{{
	printf("Initial I2C control register: 0x%08x\n", _i2c->ic_control);
	_i2c->ic_control = I2CC_CLEAR;
	do {
		c = _i2c->ic_control;
	} while(0 == (c & I2CC_STOPPED));
	printf("        Control register: 0x%08x\n", _i2c->ic_control);
	printf("Initial clock counter   : 0x%08x\n", _i2c->ic_clkcount);
	// }}}

	printf("Commanding Si5324 sequence ...\n");

	_i2c->ic_address = (unsigned)siconfig;	// Start the transmission

	do {
		c = _i2c->ic_control;
	} while(0 == (c & I2CC_STOPPED)); // While not halted and not aborted

	if (0 == (c & I2CC_ABORT)) {
		// We aborted.  Now halt.  Hard halt.
		_i2c->ic_control = I2CC_CLEAR;
	}

	printf("I2C Control = %08x\n", c);

	if (c & I2CC_FAULT) {
		printf(".. Aborted\n");
		zip_halt();
	}

	printf("Si5324 setup complete\n");

	// Set up the I2C DMA
	// {{{
	_i2cdma->id_memlen = 0;
	_i2cdma->id_base = (unsigned)&readmem[0];
	_i2cdma->id_memlen = sizeof(readmem);
	// }}}

	for(int k=0; k<10; k++) {
		unsigned	nr;

		// Wait a second ..
		// {{{
		_zip->z_tma = 100000000;	// One second
		while(_zip->z_tma != 0)
			;
		// }}}

		// Now let's read back the interrupt/warning signs
		// {{{

		// Command a DMA read
		_i2c->ic_address = (unsigned)sird;

		do {
			c = _i2c->ic_control;
		} while(0 == (c & I2CC_STOPPED)); // While not halted and not aborted

		if (c & I2CC_FAULT) {
			// We aborted.  Now halt.  Hard halt.
			_i2c->ic_control = I2CC_HARDHALT;
			printf("I2C ABORT!!\n");
			zip_halt();
		}

		CLEAR_DCACHE;

		nr = _i2cdma->id_current - _i2cdma->id_base;

printf("---\n");
		alrm = 0;
		for(int j=0; j<nr && j < sizeof(readmem); j++) {
			unsigned	ch = readmem[j] & 0x0ff;

			printf("  [%2d]: %02x\t", j, ch);
			switch(j) {
			case 0: printf("  x129, ALRM -- %3s %3s %3s\n",
				(ch & 4) ? "LOS2":"    ",
				(ch & 2) ? "LOS1":"    ",
				(ch & 1) ? "LOSX":"    ");
				alrm = alrm || (ch & 3);
				break;
			case 1: printf("  x130, ALRM -- %3s\n",
				(ch & 1) ? "LOL":"   ");
				alrm = alrm || (ch & 1);
				break;
			case 2: printf("  x131, FLAG -- %3s %3s %3s\n",
				(ch & 4) ? "LOS2":"    ",
				(ch & 2) ? "LOS ":"    ",
				(ch & 1) ? "LOSX":"    ");
				alrm = alrm || (ch & 3);
				break;
			case 3: printf("  x132, FLAG -- %3s\n",
				(ch & 2) ? "LOL_FLG":"   "); break;
			case 4: printf("  x134: PARTNUM[11:4]=%02x\n",ch);
				break;
			case 5: printf("  x135: PARTNUM[ 3:0]=%1x, DEVID=%1x\n",
				(ch >> 4)&0x0f, ch & 0x0f);
				break;
			case 6: printf("  x135, CAL  -- %3s %3s\n",
				(ch & 0x80) ? "RST":"   ",
				(ch & 0x40) ? "ICAL":"   "); break;
			default:
				printf("\n");
				break;
			}
		} if (alrm)
			k = 0;
		// }}}
	}

		// }}}
}
// }}}

int main(int argc, char **argv) {
#ifndef	VALID_CLKCHECK
	printf("clkcheck requires a valid clock to check\n");
#else
	setup_siclk();

	while(1) {
		_zip->z_tma = 100000000;	// One second
		while(_zip->z_tma != 0)
			;
printf("---\n");
#ifdef	_BOARD_HAS_NETCLK
		clkreport("NET.REF",   _netclk[5]);
		clkreport("NET.TX",    _netclk[4]);
		clkreport("NET.RX[0]", _netclk[0]);
		clkreport("NET.RX[1]", _netclk[1]);
		clkreport("NET.RX[2]", _netclk[2]);
		clkreport("NET.RX[3]", _netclk[3]);
#endif
#ifdef	_BOARD_HAS_SATAREFCOUNTER
		clkreport("SATA RefClk", (*_satarefcounter));
#endif
#ifdef	_BOARD_HAS_SATARXCOUNTER
		clkreport("SATA RX Clk", (*_satarxck));
#endif
#ifdef	_BOARD_HAS_SATATXCOUNTER
		clkreport("SATA TX Clk", (*_satatxck));
#endif
#ifdef	_BOARD_HAS_REFCLKCOUNTER
		clkreport("Si5324 RefClk", (*_sirefclkcounter));
#endif
#ifdef	_BOARD_HAS_SICLKCOUNTER
		clkreport("Si5324", (*_siclk));
#endif
#ifdef	_BOARD_HAS_VIDPIPE
		clkreport("HDMI.RX",_hdmi->v_hdmifreq);
		clkreport("Vid.Si5324", _hdmi->v_sifreq);
		clkreport("PixClk", _hdmi->v_pxfreq);
#endif
	}
#endif
}
