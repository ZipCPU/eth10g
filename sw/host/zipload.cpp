////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zipload.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To load a program for the ZipCPU into memory, whether flash
//		or SDRAM.  This requires a working/running configuration
//	in order to successfully load.
//
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
//
// }}}
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "port.h"
#include "llcomms.h"
#include "ttybus.h"
#include <design.h>
#include "regdefs.h"

#ifdef	FLASH_ACCESS
#include "flashdrvr.h"
#endif
#include "zipelf.h"
#include "byteswap.h"

DEVBUS	*m_fpga;

void	usage(void) {
	printf("USAGE: zipload [-hr] <zip-program-file>\n");
	printf("\n"
"\t-h\tDisplay this usage statement\n"
"\t-r\tStart the ZipCPU running from the address in the program file\n");
}

void	skip_bitfile_header(FILE *fp) {
	// {{{
	const unsigned	SEARCHLN = 204, MATCHLN = 52;
	const unsigned char matchstr[MATCHLN] = {
		0xff, 0xff, 0xff, 0xff,
		0xff, 0xff, 0xff, 0xff,
		0xff, 0xff, 0xff, 0xff,
		0xff, 0xff, 0xff, 0xff,
		//
		0xff, 0xff, 0xff, 0xff,
		0xff, 0xff, 0xff, 0xff,
		0xff, 0xff, 0xff, 0xff,
		0xff, 0xff, 0xff, 0xff,
		//
		0x00, 0x00, 0x00, 0xbb,
		0x11, 0x22, 0x00, 0x44,
		0xff, 0xff, 0xff, 0xff,
		0xff, 0xff, 0xff, 0xff,
		//
		0xaa, 0x99, 0x55, 0x66 };
	unsigned char	buf[SEARCHLN];
	size_t		sz;

	rewind(fp);
	sz = fread(buf, sizeof(char), SEARCHLN, fp);
	for(int start=0; start+MATCHLN<sz; start++) {
		int	mloc;

		// Search backwards, since the starting bytes just aren't that
		// interesting.
		for(mloc = MATCHLN-1; mloc >= 0; mloc--)
			if (buf[start+mloc] != matchstr[mloc])
				break;
		if (mloc < 0) {
			fseek(fp, start, SEEK_SET);
			return;
		}
	}

	fprintf(stderr, "Could not find bin-file header within bit file\n");
	fclose(fp);
	exit(EXIT_FAILURE);
}
// }}}


int main(int argc, char **argv) {
#ifndef	R_ZIPCTRL
	fprintf(stderr, "This design doesn\'t seem to contain a ZipCPU\n");
	return	EXIT_FAILURE;
#else
	int		skp=0;
	bool		start_when_finished = false, verbose = false;
	unsigned	entry = 0; // gpio;
#ifdef	FLASH_ACCESS
	FLASHDRVR	*flash = NULL;
#endif
	const char	*bitfile = NULL, *altbitfile = NULL, *execfile = NULL;

	if (argc < 2) {
		usage();
		exit(EXIT_SUCCESS);
	}

	skp=1;
	for(int argn=0; argn<argc-skp; argn++) {
		if (argv[argn+skp][0] == '-') {
			switch(argv[argn+skp][1]) {
			case 'h':
				usage();
				exit(EXIT_SUCCESS);
				break;
			case 'r':
				start_when_finished = true;
				break;
			case 'v':
				verbose = true;
				break;
			default:
				fprintf(stderr, "Unknown option, -%c\n\n",
					argv[argn+skp][0]);
				usage();
				exit(EXIT_FAILURE);
				break;
			} skp++; argn--;
		} else {
			// Anything here must be either the program to load,
			// or a bit file to load
			argv[argn] = argv[argn+skp];
		}
	} argc -= skp;


	for(int argn=0; argn<argc; argn++) {
		if (iself(argv[argn])) {
			if (execfile) {
				printf("Too many executable files given, %s and %s\n", execfile, argv[argn]);
				usage();
				exit(EXIT_FAILURE);
			} execfile = argv[argn];
		} else { // if (isbitfile(argv[argn]))
			if (!bitfile)
				bitfile = argv[argn];
			else if (!altbitfile)
				altbitfile = argv[argn];
			else {
				printf("Unknown file name or too many files, %s\n", argv[argn]);
				usage();
				exit(EXIT_FAILURE);
			}
		}
	}

	if (verbose) {
		if (bitfile)
			printf("BitFile   : %s\n", bitfile);
		else
			printf("BitFile   : No bit-file given\n");

		if (altbitfile)
			printf("AltBitFile: %s\n", altbitfile);
		else
			printf("AltBitFile: No alternate bit-file given\n");

		if (execfile)
			printf("Executable: %s\n", altbitfile);
		else
			printf("Executable: No ZipCPU executable (ELF) file given\n");
	}

	if ((execfile == NULL)&&(bitfile == NULL)) {
		printf("No executable or bit file(s) given!\n\n");
		usage();
		exit(EXIT_FAILURE);
	}

	if ((bitfile)&&(access(bitfile,R_OK)!=0)) {
		// If there's no code file, or the code file cannot be opened
		fprintf(stderr, "Cannot open bitfile, %s\n", bitfile);
		exit(EXIT_FAILURE);
	}

	if ((altbitfile)&&(access(altbitfile,R_OK)!=0)) {
		// If there's no code file, or the code file cannot be opened
		fprintf(stderr, "Cannot open alternate bitfile, %s\n", altbitfile);
		exit(EXIT_FAILURE);
	}

	if ((execfile)&&(access(execfile,R_OK)!=0)) {
		// If there's no code file, or the code file cannot be opened
		fprintf(stderr, "Cannot open executable, %s\n", execfile);
		exit(EXIT_FAILURE);
	}

	m_fpga = connect_devbus("");
#ifdef	FLASH_ACCESS
	flash = new FLASHDRVR(m_fpga);
	char	*fbuf = new char[FLASHLEN];

	// Set the flash buffer to all ones
	memset(fbuf, -1, FLASHLEN);

	if (bitfile) {
		// {{{
		FILE	*fp;
		uint64_t	sz = 0;

		if (verbose)
			fprintf(stderr, "Loading bitfile to memory ...\n");
		fp = fopen(bitfile, "rb");
		if (NULL == fp) {
			fprintf(stderr, "ERROR: Cannot open bitfile, %s\n", bitfile);
			exit(EXIT_FAILURE);
		}  if (strcmp(&bitfile[strlen(bitfile)-4], ".bit")==0) {
			skip_bitfile_header(fp);
		} sz = fread(fbuf, 1, FLASHLEN, fp);
		fclose(fp);

		try {
			if (verbose) {
				fprintf(stderr, "Loaded %d bytes\n", (unsigned)sz);
				fprintf(stderr, "Writing bitfile to flash ...\n");
			}
			flash->write(FLASHBASE, (unsigned)sz, fbuf, true);
		} catch(BUSERR b) {
			fprintf(stderr, "BUS-ERR @0x%08x\n", b.addr);
			exit(EXIT_FAILURE);
		}
	}
	// }}}
		
	if (altbitfile) {
		// {{{
		FILE	*fp;
		const unsigned	OFFSET=SECTOROF((RESET_ADDRESS-FLASHBASE)/2);
		uint64_t	sz = 0;

		fp = fopen(altbitfile, "rb");
		if (NULL == fp) {
			fprintf(stderr, "ERROR: Cannot open altbitfile, %s\n", altbitfile);
			exit(EXIT_FAILURE);
		}  if (strcmp(&bitfile[strlen(altbitfile)-4], ".bit")==0) {
			skip_bitfile_header(fp);
		} sz = fread(&fbuf[OFFSET], 1, FLASHLEN-OFFSET, fp);
		fclose(fp);

		try {
			flash->write(FLASHBASE+OFFSET, sz, &fbuf[OFFSET], true);
		} catch(BUSERR b) {
			fprintf(stderr, "BUS-ERR @0x%08x\n", b.addr);
			exit(EXIT_FAILURE);
		}
	}
	// }}}
#else
	if (bitfile || altbitfile) {
		fprintf(stderr, "WARNING: Cannot load bitfiles w/o flash");
	}
#endif

	if (verbose)
		fprintf(stderr, "ZipLoad: Verbose mode on\n");

	// Make certain we can talk to the FPGA
	try {
		unsigned v  = m_fpga->readio(R_VERSION);
		if (v < 0x20230000) {
			fprintf(stderr, "Could not communicate with board (invalid version)\n");
			exit(EXIT_FAILURE);
		}
	} catch(BUSERR b) {
		fprintf(stderr, "Could not communicate with board (BUSERR when reading VERSION)\n");
		exit(EXIT_FAILURE);
	}

	// Halt the CPU
	try {
		printf("Halting the CPU\n");
		m_fpga->writeio(R_ZIPCTRL, CPU_HALT|CPU_RESET);
	} catch(BUSERR b) {
		fprintf(stderr, "Could not halt the CPU (BUSERR)\n");
		exit(EXIT_FAILURE);
	}

	if (execfile) try {
		ELFSECTION	**secpp = NULL, *secp;
#ifdef	FLASH_ACCESS
		unsigned	startaddr = RESET_ADDRESS;
		unsigned	codelen = 0;
#endif


		if(iself(execfile)) {
			// zip-readelf will help with both of these ...
			elfread(execfile, entry, secpp);
		} else {
			fprintf(stderr, "ERR: %s is not in ELF format\n", execfile);
			exit(EXIT_FAILURE);
		}

		printf("Loading: %s\n", execfile);
		// assert(secpp[1]->m_len = 0);
		for(int i=0; secpp[i]->m_len; i++) {
			bool	valid = false;
			secp=  secpp[i];

			// Make sure our section is either within block RAM
#ifdef	BKRAM_ACCESS
			if ((secp->m_start >= BKRAMBASE)
				&&(secp->m_start+secp->m_len
						<= BKRAMBASE+BKRAMLEN))
				valid = true;
#endif

#ifdef	FLASH_ACCESS
			// Flash
			if ((secp->m_start >= RESET_ADDRESS)
				&&(secp->m_start+secp->m_len
						<= FLASHBASE+FLASHLEN))
				valid = true;
#endif

#ifdef	DDR3_CONTROLLER_ACCESS
			// Or SDRAM
			if ((secp->m_start >= DDR3_CONTROLLERBASE)
				&&((unsigned)secp->m_start+(unsigned)secp->m_len
						<= (unsigned)DDR3_CONTROLLERBASE+(unsigned)DDR3_CONTROLLERLEN))
				valid = true;
#endif
			if (!valid) {
				fprintf(stderr, "No such memory on board: 0x%08x - %08x\n",
					secp->m_start, secp->m_start+secp->m_len);
				exit(EXIT_FAILURE);
			}
		}

		for(int i=0; secpp[i]->m_len; i++) {
			secp = secpp[i];

#ifdef	DDR3_CONTROLLER_ACCESS
			if ((secp->m_start >= DDR3_CONTROLLERBASE)
				&&((unsigned)secp->m_start+(unsigned)secp->m_len
						<= (unsigned)DDR3_CONTROLLERBASE+(unsigned)DDR3_CONTROLLERLEN)) {
				if (verbose)
					printf("Writing to MEM: %08x-%08x\n",
						secp->m_start,
						secp->m_start+secp->m_len);
				unsigned ln = (secp->m_len+3)&-4;
				uint32_t	*bswapd = new uint32_t[ln>>2];
				if (ln != (secp->m_len&-4))
					memset(bswapd, 0, ln);
				memcpy(bswapd, secp->m_data,  ln);
				byteswapbuf(ln>>2, bswapd);
				m_fpga->writei(secp->m_start, ln>>2, bswapd);

				continue;
			}
#endif

#ifdef	BKRAM_ACCESS
			if ((secp->m_start >= BKRAMBASE)
				  &&(secp->m_start+secp->m_len
						<= BKRAMBASE+BKRAMLEN)) {
				if (verbose)
					printf("Writing to MEM: %08x-%08x\n",
						secp->m_start,
						secp->m_start+secp->m_len);
				unsigned ln = (secp->m_len+3)&-4;
				uint32_t	*bswapd = new uint32_t[ln>>2];
				if (ln != (secp->m_len&-4))
					memset(bswapd, 0, ln);
				memcpy(bswapd, secp->m_data,  ln);
				byteswapbuf(ln>>2, bswapd);
				m_fpga->writei(secp->m_start, ln>>2, bswapd);
				continue;
			}
#endif

#ifdef	FLASH_ACCESS
			if ((secp->m_start >= FLASHBASE)
				  &&(secp->m_start+secp->m_len
						<= FLASHBASE+FLASHLEN)) {
				// Otherwise writing to flash
				if (secp->m_start < startaddr) {
					// Keep track of the first address in
					// flash, as well as the last address
					// that we will write
					codelen += (startaddr-secp->m_start);
					startaddr = secp->m_start;
				} if (secp->m_start+secp->m_len > startaddr+codelen) {
					codelen = secp->m_start+secp->m_len-startaddr;
				} if (verbose)
					printf("Sending to flash: %08x-%08x\n",
						secp->m_start,
						secp->m_start+secp->m_len);

				// Copy this data into our copy of what we want
				// the flash to look like.
				memcpy(&fbuf[secp->m_start-FLASHBASE],
					secp->m_data, secp->m_len);
			}
#endif
		}

#ifdef	FLASH_ACCESS
		if (codelen == 0) {
			// Nothing to do here
		} else if (!flash) {
			fprintf(stderr, "ERR: Cannot write to flash: No driver\n");
		} else {
			if (verbose)
				fprintf(stderr, "Writing ZipCPU image to flash\n");
			if (!flash->write(startaddr, codelen, &fbuf[startaddr-FLASHBASE], true)) {
				fprintf(stderr, "ERR: Could not write program to flash\n");
				exit(EXIT_FAILURE);
			}
		}
#endif
		// m_fpga->writeio(R_GPIO, 0x0400040);	// Turn tracing on

		if (m_fpga) m_fpga->readio(R_VERSION); // Check for bus errors

		// Now ... how shall we start this CPU?
		printf("Clearing the CPUs registers\n");
		{
			unsigned r[32];
			m_fpga->writeio(R_ZIPCTRL, CPU_HALT);
			for(int i=0; i<32; i++)
				r[i] = 0;
			m_fpga->writei(R_ZIPREGS, 32, r);
		}

		m_fpga->writeio(R_ZIPCTRL, CPU_HALT|CPU_CLRCACHE);
		printf("Setting PC to %08x\n", entry);
		m_fpga->writeio(R_ZIPPC, entry);

		if (start_when_finished) {
			printf("Starting the CPU\n");
			m_fpga->writeio(R_ZIPCTRL, CPU_GO);
		} else {
			printf("The CPU should be fully loaded, you may now\n");
			printf("start it (from reset/reboot) with:\n");
			printf("> wbregs cpu 0\n");
			printf("\n");
		}
	} catch(BUSERR a) {
		fprintf(stderr, "ZBASIC-BUS error: %08x\n", a.addr);
		exit(-2);
	}

	printf("CPU Status is: %08x\n", m_fpga->readio(R_ZIPCTRL));
	if (m_fpga) delete	m_fpga;

	return EXIT_SUCCESS;
#endif
}

