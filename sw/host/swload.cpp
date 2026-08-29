////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/swload.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Flash an entire image (bit files and ZipCPU program) in one	command:
//	  % swload [-r] <zipcpu-loader> <golden.bit> <alt.bit> <zipcpu-program>
//
//	Writing flash from the host over the debug bus takes hours, because
//	every byte crosses a serial link.  Instead this stages the payload in
//	SDRAM once, then hands a descriptor to a small loader running on the
//	ZipCPU, which writes flash at hardware speed.
//
//	The other half of this is sw/zipcpu/board/swloader.c; the constants
//	they share come from autodata/swload.txt.
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

#include <stdio.h>
#include <stdlib.h>
#include "port.h"
#include "llcomms.h"
#include "ttybus.h"
#include <design.h>
#include "regdefs.h"
#include <unistd.h>
#include "zipelf.h"
#include "byteswap.h"
#include <string.h>

#ifdef	DDR3_CONTROLLERBASE
#define SWLOAD_DESC_ADDR   (DDR3_CONTROLLERBASE + 4)
#define PAYLOAD_ADDR   (DDR3_CONTROLLERBASE + 0x1000)  // above the descriptor, in SDRAM
#else
#define SWLOAD_DESC_ADDR   (SDRAMBASE + 4)
#define PAYLOAD_ADDR   (SDRAMBASE + 0x1000)  // above the descriptor, in SDRAM
#endif

// The golden image sits at the bottom of flash, the alternate image halfway
// between it and the ZipCPU program, and the program itself at the CPU's reset address.
// Each image therefore gets the space up to the next one.
#define RESET_IN_FLASH ((RESET_ADDRESS >= FLASHBASE) \
	&& (RESET_ADDRESS < FLASHBASE + FLASHLEN))
#define	GOLDEN_ADDR    FLASHBASE
#define	ALT_ADDR       (FLASHBASE + SECTOROF((RESET_ADDRESS - FLASHBASE)/2))
#define	IMAGE_MAXLEN   (ALT_ADDR - GOLDEN_ADDR)

void usage(void) {
	// {{{
	printf("USAGE: swload [-hrv] <zipcpu-loader> <golden.bit> <alt.bit> <zipcpu-program>\n");
	printf("\n"
	"\t-h\tDisplay this usage statement\n"
	"\t-r\tRestart the ZipCPU from flash when finished\n"
	"\t-v\tVerbose\n"
	"\n"
	"Files are recognised by content, not position: ELF files are taken\n"
	"as the loader then the program, non-ELF files as the golden then\n"
	"the alternate bit image. Any of them may be omitted.\n"
	"\n"
	"Flash layout:  golden %08x, alternate %08x, program %08x\n",
	GOLDEN_ADDR, ALT_ADDR, RESET_ADDRESS);
}
// }}}

// Halt and reset the CPU, load the loader into block RAM, and start it
// running there. The loader then waits for a descriptor in SDRAM.
static void load_loader(DEVBUS *fpga, const char *fname, bool verbose) {
	// {{{
	ELFSECTION **secpp = NULL;
	unsigned entry = 0;

	// Always start with reset.
	fpga->writeio(R_ZIPCTRL, CPU_HALT|CPU_RESET);

	elfread(fname, entry, secpp);

	for(int i=0; secpp[i]->m_len; i++) {
		ELFSECTION *s = secpp[i];
		if (verbose)
			printf("  Loading S/W into:     %08x - %08x\n", s->m_start, s->m_start + s->m_len - 1);
		unsigned nw = (s->m_len + 3) / 4;
		char *buf = new char[nw*4];

		memset(buf, 0, nw*4);
		memcpy(buf, s->m_data, s->m_len);
		byteswapbuf(nw, (uint32_t *)buf);
		fpga->writei(s->m_start, nw, (uint32_t *)buf);
		delete[] buf;
	}

	fpga->writeio(R_ZIPCTRL, CPU_HALT|CPU_CLRCACHE);
	fpga->writeio(R_ZIPPC, entry);
	fpga->writeio(R_ZIPCTRL, CPU_GO | 0x20);

	if (verbose)
		printf("  Starting ZipCPU from: %08x\n", entry);
}
// }}}

// A simple additive checksum over the staged words.
static unsigned swload_checksum(const uint32_t *buf, unsigned nw) {
	// {{{
	unsigned sum = 0;
	for(unsigned i=0; i<nw; i++)
		sum += buf[i];
	return sum;
}
// }}}

// Copy one blob into SDRAM and describe it in the descriptor as a region.
//
//    +0 d_command   +4 d_magic   +8 d_nregions   then 16 bytes per region
//    region: +0 r_src  +4 r_dst  +8 r_len  +12 r_checksum
//
// Returns the next free staging address and bumps *nregions.
static unsigned stage_region(DEVBUS *fpga, const char *data, unsigned len,
	unsigned flashaddr, unsigned staged, unsigned *nregions,
	const char *what, bool verbose) {
	// {{{
	if (*nregions >= SWLOAD_MAX_REGIONS) {
		fprintf(stderr, "ERR: Too many flash regions (max %d)\n",
			SWLOAD_MAX_REGIONS);
		exit(EXIT_FAILURE);
	}

	// Pad up to a word boundary with 0xff.
	unsigned nw = (len + 3) / 4;
	uint32_t *buf = new uint32_t[nw];
	memset(buf, 0xff, nw*4);
	memcpy(buf, data, len);
	byteswapbuf(nw, buf);

	unsigned cksum = swload_checksum(buf, nw);
	printf("Stage #%2d loading: 0x%08x + %d -> %08x\n", *nregions, staged, nw, flashaddr);
	fpga->writei(staged, nw, buf);
	delete[] buf;

	unsigned ra = SWLOAD_DESC_ADDR + 12 + (*nregions)*16;
	fpga->writeio(ra +  0, staged);
	fpga->writeio(ra +  4, flashaddr);
	fpga->writeio(ra +  8, len);
	fpga->writeio(ra + 12, cksum);

	if (verbose)
		printf("  Loaded %s\n", what);

	(*nregions)++;
	return staged + ((len + 63) & ~63);
}
// }}}

// Stage a raw (non-ELF) file, a .bit image. There are no sections to walk.
// The whole file is one contiguous blob at a fixed flash offset.
static unsigned stage_bitfile(DEVBUS *fpga, const char *fname,
	unsigned flashaddr,
	unsigned staged, unsigned *nregions, bool verbose) {
	// {{{
	char	*data;
	FILE *fp = fopen(fname, "rb");
	if (NULL == fp) {
		fprintf(stderr, "ERR: Cannot open %s\n", fname);
		perror(fname);
		exit(EXIT_FAILURE);
	}

	// Measure the size
	fseek(fp, 0, SEEK_END);
	long len = ftell(fp);
	fseek(fp, 0, SEEK_SET);

	if (len <= 0) {
		fprintf(stderr, "ERR: %s is empty\n", fname);
		exit(EXIT_FAILURE);
	}

//    if ((unsigned)len > IMAGE_MAXLEN) {
//        fprintf(stderr, "ERR: %s is %ld bytes, max is %u\n", fname, len, IMAGE_MAXLEN);
//        exit(EXIT_FAILURE);
//    }

	data = new char[len];
	if (1 != fread(data, len, 1, fp)) {
		fprintf(stderr, "ERR: Short read on %s\n", fname);
		exit(EXIT_FAILURE);
	} fclose(fp);

	staged = stage_region(fpga, data, (unsigned)len, flashaddr, staged,
		nregions, fname, verbose);
	delete[] data;
	return staged;
}
// }}}

// Stage an ELF program: one region per section that lands in flash. Sections
// outside flash (block RAM, SDRAM) are not ours to write.
static unsigned stage_program(DEVBUS *fpga, const char *fname, unsigned staged,
	unsigned *nregions, bool verbose) {
	// {{{
	ELFSECTION **secpp = NULL;
	unsigned entry = 0;

	elfread(fname, entry, secpp);
	if (verbose)
	printf("  entry point: %08x\n", entry);

	for(int i=0; secpp[i]->m_len; i++) {
	ELFSECTION *s = secpp[i];

	if (s->m_start < FLASHBASE || s->m_start >= FLASHBASE + FLASHLEN)
	continue;

	staged = stage_region(fpga, s->m_data, s->m_len, s->m_start, staged,
	nregions, fname, verbose);
	}

	return staged;
}
// }}}

int main(int argc, char **argv) {
	// Local definitions
	// {{{
	bool start_when_finished = false, verbose = false;
	const char *loaderfile = NULL, *execfile = NULL;
	const char *bitfile = NULL, *altbitfile = NULL;
	int c;
	int stalled = 0;
	unsigned nregions = 0;
	unsigned status, hb, last_hb = 0;
	unsigned staged = PAYLOAD_ADDR;
	// }}}

	// Argument parser
	// {{{
	if (argc <= 1) {
		usage();
		exit(EXIT_FAILURE);
	} else while ((c = getopt(argc, argv, "hrv")) != -1) {
		switch(c) {
			case 'r': start_when_finished = true; break;
			case 'v': verbose = true; break;
			case 'h': usage(); exit(EXIT_SUCCESS);
			default:  usage(); exit(EXIT_FAILURE);
		}
	}

	for (int i = optind; i < argc; i++) {
		if (iself(argv[i])) {
			if (!loaderfile)
				loaderfile = argv[i];   // First ELF: loader
			else if (!execfile)
				execfile   = argv[i];   // Second: program
			else {
				fprintf(stderr, "ERR: Too many ELF files\n");
				usage();
				exit(EXIT_FAILURE);
			}
		} else {
			if (!bitfile)
				bitfile = argv[i];
			else if (!altbitfile)
				altbitfile = argv[i];
			else {
				fprintf(stderr, "ERR: Too many bit files\n");
				usage();
				exit(EXIT_FAILURE);
			}
		}
	}
	// }}}

	// Verbose
	// {{{
	if (verbose) {
	printf("Loader    : %s\n", loaderfile ? loaderfile : "(none)");
	printf("Golden    : %s\n", bitfile    ? bitfile    : "(none)");
	printf("Alternate : %s\n", altbitfile ? altbitfile : "(none)");
	printf("Program   : %s\n", execfile   ? execfile   : "(none)");
	}
	// }}}

	DEVBUS *m_fpga;
	m_fpga = connect_devbus(NULL);

	{
		unsigned v = m_fpga->readio(R_VERSION);
		unsigned t = m_fpga->readio(R_BUILDTIME);
		printf("FPGA Config: %08x / %08x\n", v, t);
	}

	if (loaderfile) {
		printf("Loading %s ...\n", loaderfile);
		load_loader(m_fpga, loaderfile, verbose);
	}

	// Bit files
	// {{{
	if ((bitfile || altbitfile) && !RESET_IN_FLASH) {
	fprintf(stderr, "ERR: this design's reset vector (%08x) is not in "
		"flash,\n     so the bit image offsets are meaningless\n",
		RESET_ADDRESS);
		exit(EXIT_FAILURE);
	}

	if (bitfile)
		staged = stage_bitfile(m_fpga, bitfile, GOLDEN_ADDR, staged,
			&nregions, verbose);
	if (altbitfile)
		staged = stage_bitfile(m_fpga, altbitfile, ALT_ADDR, staged,
			&nregions, verbose);
	// }}}

	// Program
	// {{{
	if (execfile)
		staged = stage_program(m_fpga, execfile, staged, &nregions, verbose);
	// }}}

#ifdef	R_ZIPSCOPE
	m_fpga->writeio(R_ZIPSCOPE, 0x00fc);
#endif
	m_fpga->writeio(SWLOAD_DESC_ADDR + 4, SWLOAD_MAGIC);   // d_magic
	m_fpga->writeio(SWLOAD_DESC_ADDR + 8, nregions);       // d_nregions
	m_fpga->writeio(SWLOAD_DESC_ADDR + 0, 1);   // d_command = GO

	printf("magic    = %08x\n", m_fpga->readio(SWLOAD_DESC_ADDR + 4));
	printf("nregions = %08x\n", m_fpga->readio(SWLOAD_DESC_ADDR + 8));
	printf("command  = %08x\n", m_fpga->readio(SWLOAD_DESC_ADDR + 0));

	// Wait for the loader
	// {{{
	// Heartbeat only advances once per region, so the timeout has to
	// cover a whole region. Flash writes are slow in simulation.
	if (nregions == 0) {
		printf("Nothing to flash\n");
		delete m_fpga;
		return EXIT_SUCCESS;
	}

	printf("Waiting ...\n");
	while (true) {
		status = m_fpga->readio(SWLOAD_DESC_ADDR + 0);
#ifdef	DDR3_CONTROLLERBASE
		hb     = m_fpga->readio(DDR3_CONTROLLERBASE);
#else
		hb     = m_fpga->readio(SDRAMBASE);
#endif

		if (status == SWLOAD_STAT_DONE) {
			printf("DONE\n");
			break;
		} else if (status == SWLOAD_STAT_FAIL) {
			printf("FAILED at heardbeat 0x%08x\n", hb);
			break;
		}

		if (hb != last_hb) {
			last_hb = hb;
			stalled = 0;
		} else if (stalled > 180) {      // ~10 minutes
			printf("No progress, giving up\n");
			break;
		}

printf("Heart-Beats: %08x\n", hb);
		stalled = stalled + 1;
		usleep(200000);
	}
	// }}}

	// Completion sequencing
	// {{{
	// The flash now holds a new program, but the CPU is still running the
	// loader out of block RAM with a stale cache. Reset it so it restarts
	// from the flash reset vector.
	if (status == SWLOAD_STAT_DONE) {
	m_fpga->writeio(R_ZIPCTRL, CPU_HALT|CPU_RESET|CPU_CLRCACHE);

		if (start_when_finished) {
			printf("Restarting the CPU from flash\n");
			m_fpga->writeio(R_ZIPCTRL, CPU_GO);
		} else {
			printf("The CPU is halted in reset. Start it with:\n");
			printf("> wbregs cpu 0\n");
	}
	}
	// }}}

	delete m_fpga;
	return (status == SWLOAD_STAT_DONE) ? EXIT_SUCCESS : EXIT_FAILURE;
}
