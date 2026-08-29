////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/flashdev.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Flash driver.  Encapsulates the erasing and programming (i.e.
//		writing) necessary to set the values in a flash device.
//
//	This file is different from sw/host/flashdrvr.cpp in that 1) it is
//	C and not C++, and 2) it is intended to be run from the ZipCPU--rather
//	than from an external host.  The difference speeds up the operation
//	very significantly.
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
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

// #include "design.h"
#include "board.h"
#include "../../host/regdefs.h"
#include "flashdev.h"
#include "txfns.h"
#include "zipcpu.h"
#include "oledfont.h"
#include "oledfb.h"

#define	NO_OLED

#ifdef	_BOARD_HAS_FLASHSCOPE
#define	SET_SCOPE	_flashdbg->s_ctrl = 0x04000000
#define	TRIGGER_SCOPE	_flashdbg->s_ctrl = 0xff000000
#else
#define	SET_SCOPE
#define	TRIGGER_SCOPE
#endif

#ifndef	FLASH_UNKNOWN
#define	FLASH_UNKNOWN	0
#endif

#define	MICRON_FLASHID	0x20ba1810

#define	CFG_USERMODE	(1<<12)
#ifdef	QSPI_FLASH
#define	CFG_QSPEED	(1<<11)
#endif
#ifdef	DSPI_FLASH
#define	CFG_DSPEED (1<<10)
#endif
#define	CFG_WEDIR	(1<<9)
#define	CFG_USER_CS_n	(1<<8)

const	int	HIGH_SPEED = 0;
static	const	int	DEBUG = 1;
#ifdef	FLASH_ACCESS
const	int	OPT_ADDR32 = (FLASHLEN > (1<<24));
const	unsigned FLASH_ADDR_MASK = (FLASHLEN -1);
#else
const	int	OPT_ADDR32 = 0;
const	unsigned FLASH_ADDR_MASK = -1;
#endif

static const unsigned	F_RESET = (CFG_USERMODE|0x0ff),
			F_EMPTY = (CFG_USERMODE|0x000),
			F_WRR   = (CFG_USERMODE|0x001),
			F_PP    = (OPT_ADDR32)
					? (CFG_USERMODE|0x012)
					: (CFG_USERMODE|0x002),
			F_QPP   = (OPT_ADDR32)
					? (CFG_USERMODE|0x034)
					: (CFG_USERMODE|0x032),
			F_READ  = (OPT_ADDR32)
					? (CFG_USERMODE|0x013)
					: (CFG_USERMODE|0x003),
			F_WRDI  = (CFG_USERMODE|0x004),
			F_RDSR1 = (CFG_USERMODE|0x005),
			F_WREN  = (CFG_USERMODE|0x006),
			F_MFRID = (CFG_USERMODE|0x09f),
			F_SE    = (OPT_ADDR32)	// Sector erase
					? (CFG_USERMODE|0x0dc)
					: (CFG_USERMODE|0x0d8),
			F_END   = (CFG_USERMODE|CFG_USER_CS_n);

#ifdef	R_FLASHSCOPE // Scope for the flash driver
# define SETSCOPE	_flashdbg->s_ctrl = 8180
#else
# define SETSCOPE
#endif

int	fl_debug = DEBUG;
unsigned	fl_id = FLASH_UNKNOWN;

unsigned fl_flashid(void) {
	// {{{
#ifndef	_BOARD_HAS_FLASHCFG
	return FLASH_UNKNOWN;
#else
	unsigned	r;
	if (fl_id != FLASH_UNKNOWN)
		return fl_id;

	fl_take_offline();

	*_flashcfg = CFG_USERMODE | 0x9f;
	*_flashcfg = CFG_USERMODE | 0x00;
	r = *_flashcfg & 0x0ff;
	*_flashcfg = CFG_USERMODE | 0x00;
	r = (r<<8) | (*_flashcfg & 0x0ff);
	*_flashcfg = CFG_USERMODE | 0x00;
	r = (r<<8) | (*_flashcfg & 0x0ff);
	*_flashcfg = CFG_USERMODE | 0x00;
	r = (r<<8) | (*_flashcfg & 0x0ff);
	fl_id = r;
	fl_place_online();


// printf("flash ID returning %08x\n", m_id);
	return fl_id;
#endif
}
// }}}

void	fl_take_offline(void) {
	// {{{
	*_flashcfg = F_END;
	*_flashcfg = F_RESET;
	*_flashcfg = F_RESET;
	*_flashcfg = F_RESET;
	*_flashcfg = F_RESET;
	*_flashcfg = F_RESET;
	*_flashcfg = F_RESET;
	*_flashcfg = F_END;
}
// }}}

void	fl_place_online(void) {
	// {{{
	fl_restore_quadio();
}
// }}}

void	fl_restore_quadio(void) {
		// {{{
	static	const	uint32_t	QUAD_IO_READ     = CFG_USERMODE
			|(OPT_ADDR32 ? 0xec : 0xeb);

	*_flashcfg = F_END;

	if (1) { // if (MICRON_FLASHID == m_id)
		// printf("MICRON-flash\n");
		// Need to enable XIP first for MICRON's flash
		//
		// This requires sending a write enable first
		*_flashcfg = F_WREN;
		*_flashcfg = F_END;

		// Then sending a 0xab, 0x81
		*_flashcfg = CFG_USERMODE | 0x81;
		*_flashcfg = CFG_USERMODE | 0x83;
		*_flashcfg = F_END;
	}

	*_flashcfg = QUAD_IO_READ;
	// 3 address bytes
	*_flashcfg = CFG_USERMODE | CFG_QSPEED | CFG_WEDIR;
	*_flashcfg = CFG_USERMODE | CFG_QSPEED | CFG_WEDIR;
	*_flashcfg = CFG_USERMODE | CFG_QSPEED | CFG_WEDIR;
	// 4 address bytes if in 32bit mode
	if (OPT_ADDR32)
		*_flashcfg = CFG_USERMODE | CFG_QSPEED | CFG_WEDIR;

	// Mode byte
	*_flashcfg = CFG_USERMODE | CFG_QSPEED | CFG_WEDIR | 0xa0;
	// Read NDUMMY clocks worth
#ifdef	FLASH_NDUMMY
	for(int k=0; k<(FLASH_NDUMMY-2)/2; k++)
		*_flashcfg = CFG_USERMODE | CFG_QSPEED;
#endif
	// Read a dummy byte
	*_flashcfg = CFG_USERMODE | CFG_QSPEED;
	// Raise CS#, then close the interface
	*_flashcfg = CFG_USERMODE;
	*_flashcfg = CFG_USER_CS_n;
}
// }}}

void	flwait(void) {
	// {{{
	const	int	WIP = 1;	// Write in progress bit
	unsigned	sr;

	*_flashcfg = F_END;
	*_flashcfg = F_RDSR1;
	do {
		*_flashcfg = F_EMPTY;

		sr = *_flashcfg;
	} while(sr&WIP);
	*_flashcfg = F_END;
}
// }}}

int	fl_erase_sector(const unsigned sector, const int verify_erase){
	// {{{
	unsigned	flashaddr = sector & FLASH_ADDR_MASK;
	unsigned	page[SZPAGEW];

	fl_take_offline();

	// Write enable
	*_flashcfg = F_END;
	*_flashcfg = F_WREN;
	*_flashcfg = F_END;

	// printf("EREG before   : %08x\n", m_fpga->readio(R_QSPI_EREG));

	*_flashcfg = F_SE;
	if (OPT_ADDR32)
		*_flashcfg = CFG_USERMODE|((flashaddr>>24)&0x0ff);
	*_flashcfg = CFG_USERMODE | ((flashaddr>>16)&0x0ff);
	*_flashcfg = CFG_USERMODE | ((flashaddr>> 8)&0x0ff);
	*_flashcfg = CFG_USERMODE | ((flashaddr    )&0x0ff);
	*_flashcfg = F_END;

	// Wait for the erase to complete
	flwait();

	// Turn quad-mode read back on, so we can read next
	fl_place_online();
	CLEAR_DCACHE;

	// Now, let's verify that we erased the sector properly
	if (verify_erase) {
		if (fl_debug)
			txstr("Verifying the erase\n");

		for(int i=0; i<NPAGES; i++) {
			unsigned *fp;
			char	*fpc, *flashc = (char *)_flash;
			// printf("READI[%08x + %04x]\n", R_FLASH+flashaddr+i*SZPAGEB, SZPAGEW);
			fpc = &flashc[flashaddr + i*SZPAGEB];
			fp = (unsigned *)fpc;
			for(int k=0; k<SZPAGEW; k++)
				page[k] = fp[k];
			for(int j=0; j<SZPAGEW; j++)
				if (page[j] != 0xffffffff) {
					unsigned rdaddr = (unsigned)fp+j;

					TRIGGER_SCOPE;
					if (DEBUG) {
						txstr("FLASH["); txhex((unsigned)fp+j);
						txstr("] = "); txhex(page[j]);
						txstr(", not 0xffffffff as desired\n");
					}
					return 0;
				}
		}
		if (fl_debug)
			txstr("Erase verified\n");
	}

	return 1;
}
// }}}


// Format a 32-bit value as "0x" + 8 hex digits into buf (needs 11 bytes).
// Avoids sprintf, which drags the whole stdio/float formatting machinery into
// a loader that has to fit in block RAM.
static void	hex8(char *buf, unsigned v) {
	static const char	digits[] = "0123456789abcdef";

	buf[0] = '0'; buf[1] = 'x';
	for(int i=0; i<8; i++)
		buf[2+i] = digits[(v >> ((7-i)*4)) & 0x0f];
	buf[10] = '\0';
}

int	fl_page_program(const unsigned addr, const unsigned len,
		const char *data, const int verify_write) {
	// {{{
	unsigned	buf[SZPAGEW];
	unsigned	flashaddr = addr & FLASH_ADDR_MASK;
	int	empty_page = 1;
	char	*bufc = (char *)buf;

	assert(len > 0);
	assert(len <= PGLENB);
	assert(PAGEOF(addr)==PAGEOF(addr+len-1));

	if (len == 0)
		return 1;

	for(unsigned i=0; i<len; i++) {
		if (0x0ff != data[i])
			empty_page = 0;
	}

	if (empty_page) {
		// fl_place_online();
		return 1;
	}

	fl_take_offline();

	// Write enable
	*_flashcfg = F_END;
	*_flashcfg = F_WREN;
	*_flashcfg = F_END;

	//
	// Write the page
	//

	// Issue the page program command
	//
	// Our interface will limit us, so there's no reason to use
	// QUAD page programming here
	// if (F_QPP) {} else
	*_flashcfg = F_PP;
	// The address of the page to be programmed
	if (OPT_ADDR32)
		*_flashcfg = CFG_USERMODE|((flashaddr>>24)&0x0ff);
	*_flashcfg = CFG_USERMODE|((flashaddr>>16)&0x0ff);
	*_flashcfg = CFG_USERMODE|((flashaddr>> 8)&0x0ff);
	*_flashcfg = CFG_USERMODE|((flashaddr    )&0x0ff);

	//
	// Write the page data itself
	//
	if (len > 0) {
		for(unsigned i=0; i<len; i++)
			*_flashcfg = CFG_USERMODE | CFG_WEDIR | (data[i] & 0x0ff);
	} *_flashcfg = F_END;

	txstr("Writing page:  0x"); txhex(addr);
	txstr(" - 0x"); txhex(addr+len-1);
	if (!(fl_debug && verify_write))
		txstr("\n");

	// Wait for the write to complete
	flwait();

	// Turn quad-mode read back on, so we can verify the program
	fl_place_online();
	CLEAR_DCACHE;
	if (verify_write) {
		int	passed = 1;

		// printf("Attempting to verify page\n");
		// NOW VERIFY THE PAGE
		memcpy(buf, (void *)addr, len);
		for(unsigned i=0; i<len; i++) {
			if (bufc[i] != data[i]) {
				TRIGGER_SCOPE;
				txstr("\nVERIFY FAILS at 0x"); txhex(i+addr);
				txstr(" CFG="); txhex(*_flashcfg);
				txstr("\n\tflash="); txhex(bufc[i] & 0x0ff);
				txstr(" goal="); txhex(data[i] & 0x0ff);
				txstr("\n");
				passed = 0;
			}
		} if (!passed)
			return 0;
		else if (fl_debug)
			txstr(" -- Successfully verified\n");
	} return 1;
}
// }}}

#ifdef	R_QSPI_VCONF
#define	VCONF_VALUE	0xab
#define	VCONF_VALUE_ALT	0xa3
#endif

int	fl_write(const unsigned addr, const unsigned len,
		const char *data, const int verify) {
	// {{{
	if (fl_debug)
		txstr("FL-WRITE\n");
	char	msg[64];

#ifndef	NO_OLED
	fb_font = shortfontp;
	oled_move(0, 2); oled_clear_eol();
	oled_move(0, 3); oled_clear_eol();
#endif

	SET_SCOPE;
	fl_flashid();

	// Work through this one sector at a time.
	// If this buffer is equal to the sector value(s), go on
	// If not, erase the sector

	char *sbuf = (char *)malloc(SECTORSZB);
	for(unsigned s=SECTOROF(addr); s<SECTOROF(addr+len+SECTORSZB-1);
			s+=SECTORSZB) {
		// Do we need to erase?
		int	need_erase = 0, need_program = 0;
		unsigned newv = 0; // (s<addr)?addr:s;
		{
			char	*basep;
			const char *dp;	// pointer to our "desired" buffer
			unsigned	base,ln;

			basep = (char *)((addr>s) ? addr:s);
			ln = ((addr+len>s+SECTORSZB)?(s+SECTORSZB):(addr+len))
				- (unsigned)basep;
			for(int k=0; k<ln; k++)
				sbuf[k] = basep[k];

			dp = &data[(unsigned)basep-addr];
			SETSCOPE;
			for(unsigned i=0; i<ln; i++) {
				if ((sbuf[i]&dp[i]) != dp[i]) { // Need erase
					// {{{
					if (fl_debug) {
						txstr("\nNEED-ERASE @0x"); txhex(i+(unsigned)basep-addr);
						txstr(" ... "); txhex(sbuf[i] & 0x0ff);
						txstr(" != "); txhex(dp[i] & 0x0ff);
						txstr(" (Goal)\n");
					}
					need_erase = 1;
					newv = (i&-4)+(unsigned)basep;
					break;
					// }}}
				} else if ((sbuf[i] != dp[i])&&(newv == 0))
					// Need to program
					newv = (i&-4)+(unsigned)basep;
			}
		}

		if (newv == 0)
			continue; // This sector already matches

		// Erase the sector if necessary
		if (0 == need_erase) {
			if (fl_debug) txstr("NO ERASE NEEDED\n");
		} else {
			txstr("ERASING: "); txhex(s); txstr("\n");
#ifndef	NO_OLED
			if (!oled_busy()) {	// Erasing: 0x%08x
				// {{{
				oled_move(0, 2);
				oled_write("Erasing: ");
				oled_clear_eol();
				oled_move(64, 2);
				hex8(msg, s);
				oled_write(msg);
				oled_flush();
			}
			// }}}
#endif

			if (!fl_erase_sector(s, verify)) { // Erase failed
				// {{{
				txstr("ERASE FAILED!\n");
				free(sbuf);

				fb_font = tallfontp;
#ifndef	NO_OLED
				while(oled_busy())
					;
				oled_move(0, 2); fb_font->m_fixed = 0;
				oled_write("FLASH FAILURE");
				oled_flush();
#endif

				return 0;
				// }}}
			}
			newv = (s<addr) ? addr : s;
		}

		// Now walk through all of our pages in this sector and write
		// to them.
		for(unsigned p=newv; (p<s+SECTORSZB)&&(p<addr+len);
							p=PAGEOF(p+PGLENB)) {
			unsigned start = p, ln = addr+len-start;

			// BUT! if we cross page boundaries, we need to clip
			// our results to the page boundary
			if (PAGEOF(start+len-1)!=PAGEOF(start))
				ln = PAGEOF(start+PGLENB)-start;

#ifndef	NO_OLED
			if (!oled_busy()) {	// Programming: 0x%08x
				// {{{
				oled_move(0, 2); // fb_font->m_fixed = 0;
				oled_write("Programming:"); 
				oled_clear_eol();
				oled_move(64, 2);
				hex8(msg, s);
				oled_write(msg);
				oled_flush();
			}
			// }}}
#endif

			if (!fl_page_program(start, ln, &data[p-addr], verify)){
				// {{{
				txstr("WRITE-PAGE FAILED!\n");
				free(sbuf);

				fb_font = tallfontp;
#ifndef	NO_OLED
				while(oled_busy())
					;
				oled_move(0, 0); fb_font->m_fixed = 0;
				oled_write("FLASH FAILURE");
				oled_flush();
#endif

				return 0;
			}
			// }}}
		} if ((need_erase)||(need_program)) {
			txstr("Sector 0x"); txhex(s); txstr(": DONE\n");
		}
	} free(sbuf);

	if (fl_debug)
		txstr("Taking flash back off-line\n");
	fl_take_offline();

	*_flashcfg = F_WRDI;
	*_flashcfg = F_END;

	if (fl_debug)
		txstr("Returning flash to operational\n");
	fl_place_online();

	// OLED: Program complete\n  -- Success
	// {{{
#ifndef	NO_OLED
	// SIMULATION BYPASS: I2C never asserts I2CC_HARDHALT in sim, so the
	// wait below spins forever.  The OLED writes must go with it -- driving
	// them while I2C is still busy corrupts the buffer and traps the CPU.
	while(oled_busy())
		;
	oled_move(0, 2); fb_font->m_fixed = 0;
	oled_write("Program complete\n  -- Success");
	oled_flush();
#endif
	// }}}

	return 1;
}
// }}}
