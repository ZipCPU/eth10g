////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/zipscope.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To read out, and decompose, the results of the wishbone scope
//		as applied to the ZipCPU internal operation.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2026, Gisselquist Technology, LLC
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
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>
// }}}
#include "regdefs.h"
#include "devbus.h"
#include "scopecls.h"
// }}}

#if	defined(R_ZIPSCOPE) && defined(R_ZIPSCOPED)
#define	WBSCOPE		R_ZIPSCOPE
#define	WBSCOPEDATA	R_ZIPSCOPED
#else
#define	NO_SCOPE
#define	WBSCOPE	0
#define	WBSCOPEDATA	0
#endif

#include "zopcodes.h"

DEVBUS	*m_fpga;

const char *regstr[] = {
	"R0","R1","R2","R3","R4","R5","R6","R7","R8","R9","RA","RB","RC",
	"SP","CC","PC"
};

class	ZIPSCOPE : public SCOPE {
public:
	ZIPSCOPE(DEVBUS *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, false, vecread) {};
	~ZIPSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		if (val & 0x80000000)
			printf("TRIG ");
		else
			printf("     ");

		if ((val & 0x40000000)==0) {
			printf("%s <- 0x.%07x", regstr[(val>>(32-6))&0xf], val&0x03ffffff);
		} else if ((val & 0x60000000)==0x60000000) {
			uint32_t addr = val & 0x7ffffff;
			if (val&0x08000000)
				printf("MEM-W[0x........] <- 0x.%07x %s",
					addr,
					(val&0x10000000)?"(GBL)":"");
			else
				printf("MEM-R[0x.%07x] -> (Not Givn) %s",
					(addr<<2)&0x0ffffffc,
					(val&0x10000000)?"(GBL)":"");
		} else if ((val & 0x70000000)==0x40000000) {
			val &= 0x0fffffff;
			val <<= 2;
			printf("JMP 0x%08x", (val&0x0fffffff));
		} else {
			int	master, halt, brk, sleep, buserr, trap,
				ill, clri, pfv, pfi, dcdce, dcdv, dcdstall,
				opce, opvalid, oppipe, aluce, alubsy, aluwr,
				memce, memwe, membsy;
			int	gie; // aluill, aluwrf;
			master = (val>>27)&1;
			halt   = (val>>26)&1;
			brk    = (val>>25)&1;
			sleep  = (val>>24)&1;
			gie    = (val>>23)&1;
			buserr = (val>>22)&1;
			trap   = (val>>21)&1;
			ill    = (val>>20)&1;
			clri   = (val>>19)&1;
			pfv    = (val>>18)&1;
			pfi    = (val>>17)&1;
			dcdce  = (val>>16)&1;
			dcdv   = (val>>15)&1;
			dcdstall=(val>>14)&1;
			opce   = (val>>13)&1;
			opvalid= (val>>12)&1;
			oppipe = (val>>11)&1;
			aluce  = (val>>10)&1;
			alubsy = (val>> 9)&1;
			aluwr  = (val>> 8)&1;
			// aluill = (val>> 7)&1;
			// aluwrf = (val>> 6)&1;
			memce  = (val>> 5)&1;
			memwe  = (val>> 4)&1;
			membsy = (val>> 3)&1;
			printf("FLAGS %08x", val);
			printf(" CE[%c%c%c%c]",
				(dcdce)?'D':' ',
				(opce)?'O':' ',
				(aluce)?'A':' ',
				(memce)?'M':' ');
			printf(" V[%c%c%c%c]",
				(pfv)?'P':' ',
				(dcdv)?'D':' ',
				(opvalid)?'O':' ',
				(aluwr)?'A':' ');
			if (master) printf(" MCE");
			if (halt)   printf(" I-HALT");
			if (brk)    printf(" O-BREAK");
			if (sleep)  printf(" SLP");
			if (gie)    printf(" GIE");
			if (buserr) printf(" BE");
			if (trap)   printf(" TRAP");
			if (ill)    printf(" ILL");
			if (clri)   printf(" CLR-I");
			if (pfi)    printf(" PF-ILL");
			if (dcdstall)printf(" DCD-STALL");
			if (oppipe) printf(" OP-PIPE");
			if (alubsy) printf(" ALU-BUSY");
			if (memwe)  printf(" MEM-WE");
			if (membsy) printf(" MEM-BUSY");
			//
		}
	}
};

int main(int argc, char **argv) {
#ifdef	NO_SCOPE
	printf("Design was built with no ZipCPU scope\n");
#else
	// Open and connect to our FPGA.  This macro needs to be defined in the
	// include files above.
	m_fpga = connect_devbus(NULL);

	ZIPSCOPE *scope = new ZIPSCOPE(m_fpga, WBSCOPE, true);
	if (!scope->ready()) {
		// If we get here, then ... nothing started the scope.
		// It either hasn't primed, hasn't triggered, or hasn't finished
		// recording yet.  Trying to read data would do nothing but
		// read garbage, so we don't try.
		printf("Scope is not yet ready:\n");
		scope->decode_control();
		scope->decode(WBSCOPEDATA);
		printf("\n");
	} else {
		// The scope has been primed, triggered, the holdoff wait
		// period has passed, and the scope has now stopped.
		//
		// Hence we can read from our scope the values we need.
		scope->print();
		// If we want, we can also write out a VCD file with the data
		// we just read.
	}

	// Now, we're all done.  Let's be nice to our interface and shut it
	// down gracefully, rather than letting the O/S do it in ... whatever
	// manner it chooses.
	delete	m_fpga;
#endif
}
