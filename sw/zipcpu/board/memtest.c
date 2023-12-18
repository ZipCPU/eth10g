////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	memtest.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Used to determine if the DDR3 SDRAM controller is working or
//		not.  Contains a series of tests, applied across memory, for
//	this purpose.
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
#include "zipcpu.h"
#include "board.h"

extern	char	_sdram[0x40000000];

#define	SCOPE_DELAY	16

#define	STEP(F,T)  asm volatile("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(F) : "r"(T))
#define	FAIL		asm("TRAP")

//
// memchk
// {{{
void	memchk(int *mem, int *end, unsigned seed) {
	int	counts = seed;
	// const	int	TAPS = 0x0485b5;
	// const	int	TAPS = 0x0110003;	// 2Gb
	// const	int	TAPS = 0x0280005;	// 4Gb
	const	int	TAPS = 0x0400015;	// 8Gb
	// const	int	TAPS = 0x0400019;	// 8Gb
	// const	int	TAPS = 0x0400043;	// 8Gb
	// const	int	TAPS = 0x0400051;	// 8Gb
	// const	int	TAPS = 0x04000c1;	// 8Gb
	// const	int	TAPS = 0x0400181;	// 8Gb
	// const	int	TAPS = 0x0400501;	// 8Gb
	// const	int	TAPS = 0x0401401;	// 8Gb
	// const	int	TAPS = 0x07fffdf;	// 8Gb
	char	*const endc= (char *)end;

#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Clear the bottom 3 LED's
	*_spio = 0x0e00;
	// }}}
#endif
	////////////////////////////////////////////////////////////////////////
	//
	// #1, sequential access, filled with LRS
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	{
		int	*mptr = mem;
		unsigned fill;

		// Write to memory
		// {{{
		fill = (counts == 0) ? 1 : counts;
		while(mptr < end) {
			STEP(fill, TAPS);
			// fill = (fill&1)?((fill>>1)^TAPS):(fill>>1);
			*mptr++ = fill;
		}
		// }}}

		// Read and compare
		// {{{
		fill = (counts == 0) ? 1 : counts;
		mptr = mem;
		while(mptr < end) {
			STEP(fill, TAPS);
			if (*mptr != (int)fill)
				FAIL;
			mptr++;
		}
		// }}}
	}
	// }}}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// First test done, set the bottom LED
	*_spio = 0x0e02;
	// }}}
#endif
	////////////////////////////////////////////////////////////////////////
	//
	// #2, sequential access, read/write 3x at a time
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	if (1) {
		int	*mptr = mem;
		unsigned fill;

		// Write to memory
		// {{{
		fill = counts + 4; if (fill == 0) fill = 1;
		while(mptr+3 < end) {
			register unsigned a, b, c;


			STEP(fill, TAPS);	a = fill;
			STEP(fill, TAPS);	b = fill;
			STEP(fill, TAPS);	c = fill;

			mptr[0] = a;
			mptr[1] = b;
			mptr[2] = c;

			mptr += 3;
		}
		// }}}

		// Read and compare
		// {{{
		mptr = mem;
		fill = counts + 4; if (fill == 0) fill = 1;
		while(mptr+3 < end) {
			register unsigned a, b, c;

			a = mptr[0];
			b = mptr[1];
			c = mptr[2];

			STEP(fill, TAPS);
			if (a != (int)fill)
				FAIL;

			STEP(fill, TAPS);
			if (b != (int)fill)
				FAIL;

			STEP(fill, TAPS);
			if (c != (int)fill)
				FAIL;

			mptr+=3;
		}
		// }}}
	}
	// }}}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Second test done, set the LEDs to reflect that
	*_spio = 0x0e04;
	// }}}
#endif
	////////////////////////////////////////////////////////////////////////
	//
	// #3, sequential access, read/write 3x characters at a time
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	if (1) {
		char	*mcptr;
		unsigned fill;

		// Write to memory
		// {{{
		mcptr = (char *)mem;
		fill = counts + 19; if (fill == 0) fill = 1;
		while(mcptr+3 < endc) {
			register char a, b, c;

			STEP(fill, TAPS);	a = fill; // & 0x0ff;
			STEP(fill, TAPS);	b = fill; // & 0x0ff;
			STEP(fill, TAPS);	c = fill; // & 0x0ff;

			mcptr[0] = a;
			mcptr[1] = b;
			mcptr[2] = c;

			mcptr += 3;
		}
		// }}}

		// Read and compare
		// {{{
		mcptr = (char *)mem;
		fill = counts + 19; if (fill == 0) fill = 1;
		while(mcptr+3 < endc) {
			register unsigned a, b, c;

			a = mcptr[0];
			b = mcptr[1];
			c = mcptr[2];

			STEP(fill, TAPS);
			if (((a ^ (int)fill)&0x0ff)!=0)
				FAIL;

			STEP(fill, TAPS);
			if (((b ^ (int)fill)&0x0ff)!=0)
				FAIL;

			STEP(fill, TAPS);
			if (((c ^ (int)fill)&0x0ff)!=0)
				FAIL;

			mcptr+=3;
		}
		// }}}
	}
	// }}}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Third test done
	*_spio = 0x0e06;
	// }}}
#endif
	////////////////////////////////////////////////////////////////////////
	//
	// #4, random access, read/write one word at a time
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	{
		int	*mptr = mem;
		unsigned afill, dfill, amsk, initial_afill;

		// Write to memory
		// {{{
		afill = counts;       if (afill == 0) afill = 1;
		dfill = counts + 23;  if (dfill == 0) dfill = 1;
		initial_afill = afill;
		amsk  = (end-mem) - 1;
		do {
			STEP(afill, TAPS);
			STEP(dfill, TAPS);
			if ((afill&(~amsk)) == 0)
				mptr[afill&amsk] = dfill;
		} while(afill != initial_afill);
		// }}}

		// Read and compare
		// {{{
		afill = counts;       if (afill == 0) afill = 1;
		dfill = counts + 23;  if (dfill == 0) dfill = 1;
		initial_afill = afill;
		do {
			STEP(afill, TAPS);
			STEP(dfill, TAPS);
			if ((afill & (~amsk)) == 0) {
				if (mptr[afill&amsk] != (int)dfill)
				FAIL;
			}
		} while(afill != initial_afill);
		// }}}
	}
	// }}}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Fourth test done
	*_spio = 0x0e08;

	// Toggle bit 0 (0x01) as well--since we just finished another
	// round.  This way the toggling bit will be the indication
	// that the memory controller has been successful.
	*_spio = ((*_spio&1)^1)|0x0100;
	// }}}
#endif
}
// }}}

//
// runtest(void)
// {{{
void	runtest(void) {
	int	counts = 0;
	int	*const mem = (int *)_sdram;
	int	*const end = (int *)(&_sdram[sizeof(_sdram)]);
	unsigned const BLKSIZE = (1u<<20); // 512kB, for 1<<21 < TAPS < 1<<22

#ifdef	_BOARD_HAS_SPIO
	// Clear any/all LED's
	*_spio = 0x0ff00;
#endif

#ifdef	_BOARD_HAS_ZIPSCOPE
	_zipscope->s_ctrl = SCOPE_DELAY | WBSCOPE_MANUAL;
#endif

	while(1) {
		int	*run_start, *run_end;

		counts++;
		for(run_start = mem; run_start < end - BLKSIZE;	
					run_start = run_start + BLKSIZE) {
			run_end = run_start + BLKSIZE;
			memchk(run_start, run_end, counts);
		}
	}
}
// }}}

//
// main
// {{{
// Create and start a user task that can then be halted on any error
int	main(void) {
	unsigned zero = 0;
	unsigned	usp[512];

	asm("MOV %0,uR0" : : "r"(zero));
	asm(
	"\tMOV uR0,uR1\n"
	"\tMOV uR0,uR2\n"
	"\tMOV uR0,uR3\n"
	"\tMOV uR0,uR4\n"
	"\tMOV uR0,uR5\n"
	"\tMOV uR0,uR6\n"
	"\tMOV uR0,uR7\n"
	"\tMOV uR0,uR8\n"
	"\tMOV uR0,uR9\n"
	"\tMOV uR0,uR10\n"
	"\tMOV uR0,uR11\n"
	"\tMOV uR0,uR12\n"
	);

	asm("MOV %0,uSP" : : "r"(&usp[511]));
	asm("MOV %0,uPC" : : "r"(runtest));

	zip_rtu();
#ifdef	_BOARD_HAS_ZIPSCOPE
	// If the scope hasn't (yet) triggered, trigger it now
	_zipscope->s_ctrl = SCOPE_DELAY | WBSCOPE_TRIGGER | WBSCOPE_MANUAL;
#endif
#ifdef	_BOARD_HAS_SPIO
	// Activate all LEDs
	*_spio = 0x0ffff;
#endif
	zip_halt();
}
// }}}

