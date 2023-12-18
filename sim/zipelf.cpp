////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipelf.cpp
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
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <libelf.h>
#include <assert.h>
#include <gelf.h>
#include <string.h>

#include "zipelf.h"

bool
iself(const char *fname)
{
	FILE	*fp;
	bool	ret = true;
	fp = fopen(fname, "rb");

	if (!fp)	return false;
	if (0x7f != fgetc(fp))	ret = false;
	if ('E'  != fgetc(fp))	ret = false;
	if ('L'  != fgetc(fp))	ret = false;
	if ('F'  != fgetc(fp))	ret = false;
	fclose(fp);
	return 	ret;
}

void	elfread(const char *fname, unsigned &entry, ELFSECTION **&sections)
{
	Elf	*e;
	int	fd, i;
	size_t	n;
	char	*id;
	Elf_Kind	ek;
	GElf_Ehdr	ehdr;
	GElf_Phdr	phdr;
	const	bool	dbg = false;

	if (elf_version(EV_CURRENT) == EV_NONE) {
		fprintf(stderr, "ELF library initialization err, %s\n", elf_errmsg(-1));
		perror("O/S Err:");
		exit(EXIT_FAILURE);
	} if ((fd = open(fname, O_RDONLY, 0)) < 0) {
		fprintf(stderr, "Could not open %s\n", fname);
		perror("O/S Err:");
		exit(EXIT_FAILURE);
	} if ((e = elf_begin(fd, ELF_C_READ, NULL))==NULL) {
		fprintf(stderr, "Could not run elf_begin, %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	}

	ek = elf_kind(e);
	if (ek == ELF_K_ELF) {
		; // This is the kind of file we should expect
	} else if (ek == ELF_K_AR) {
		fprintf(stderr, "Cannot run an archive!\n");
		exit(EXIT_FAILURE);
	} else if (ek == ELF_K_NONE) {
		;
	} else {
		fprintf(stderr, "Unexpected ELF file kind!\n");
		exit(EXIT_FAILURE);
	}

	if (gelf_getehdr(e, &ehdr) == NULL) {
		fprintf(stderr, "getehdr() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	} if ((i=gelf_getclass(e)) == ELFCLASSNONE) {
		fprintf(stderr, "getclass() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	} if ((id = elf_getident(e, NULL)) == NULL) {
		fprintf(stderr, "getident() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	} if (i != ELFCLASS32) {
		fprintf(stderr, "This is a 64-bit ELF file, ZipCPU ELF files are all 32-bit\n");
		exit(EXIT_FAILURE);
	}

	if (dbg) {
	printf("ELF File header\n");
	printf("    %-20s 0x%jx\n", "e_type", (uintmax_t)ehdr.e_type);
	printf("    %-20s 0x%jx\n", "e_machine", (uintmax_t)ehdr.e_machine);
	printf("    %-20s 0x%jx\n", "e_version", (uintmax_t)ehdr.e_version);
	printf("    %-20s 0x%jx\n", "e_entry", (uintmax_t)ehdr.e_entry);
	printf("    %-20s 0x%jx\n", "e_phoff", (uintmax_t)ehdr.e_phoff);
	printf("    %-20s 0x%jx\n", "e_shoff", (uintmax_t)ehdr.e_shoff);
	printf("    %-20s 0x%jx\n", "e_flags", (uintmax_t)ehdr.e_flags);
	printf("    %-20s 0x%jx\n", "e_ehsize", (uintmax_t)ehdr.e_ehsize);
	printf("    %-20s 0x%jx\n", "e_phentsize", (uintmax_t)ehdr.e_phentsize);
	printf("    %-20s 0x%jx\n", "e_shentsize", (uintmax_t)ehdr.e_shentsize);
	printf("\n");
	}


	// Check whether or not this is an ELF file for the ZipCPU ...
	if (ehdr.e_machine != 0x0dad1) {
		fprintf(stderr, "This is not a ZipCPU/8 ELF file\n");
		exit(EXIT_FAILURE);
	}

	// Get our entry address
	entry = ehdr.e_entry;


	// Now, let's go look at the program header
	if (elf_getphdrnum(e, &n) != 0) {
		fprintf(stderr, "elf_getphdrnum() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	}

assert(n != 0);

	unsigned total_octets = 0, current_offset=0, current_section=0;
	for(i=0; i<(int)n; i++) {
		total_octets += sizeof(ELFSECTION *)+sizeof(ELFSECTION);

		if (gelf_getphdr(e, i, &phdr) != &phdr) {
			fprintf(stderr, "getphdr() failed: %s\n", elf_errmsg(-1));
			exit(EXIT_FAILURE);
		}

		if (dbg) {
		printf("  Section %d:\n", i);
		printf("    %-20s 0x%x\n", "p_type",   phdr.p_type);
		printf("    %-20s 0x%jx\n", "p_offset", phdr.p_offset);
		printf("    %-20s 0x%jx\n", "p_vaddr",  phdr.p_vaddr);
		printf("    %-20s 0x%jx\n", "p_paddr",  phdr.p_paddr);
		printf("    %-20s 0x%jx\n", "p_filesz", phdr.p_filesz);
		printf("    %-20s 0x%jx\n", "p_memsz",  phdr.p_memsz);
		printf("    %-20s 0x%x [", "p_flags",  phdr.p_flags);

		if (phdr.p_flags & PF_X)	printf(" Execute");
		if (phdr.p_flags & PF_R)	printf(" Read");
		if (phdr.p_flags & PF_W)	printf(" Write");
		printf("]\n");
		printf("    %-20s 0x%jx\n", "p_align", phdr.p_align);
		}

		total_octets += phdr.p_memsz;
	}

	char	*d = (char *)malloc(total_octets + sizeof(ELFSECTION)+sizeof(ELFSECTION *));
	memset(d, 0, total_octets);

	ELFSECTION **r = sections = (ELFSECTION **)d;
	current_offset = (n+1)*sizeof(ELFSECTION *);
	current_section = 0;

	for(i=0; i<(int)n; i++) {
		r[i] = (ELFSECTION *)(&d[current_offset]);

		if (gelf_getphdr(e, i, &phdr) != &phdr) {
			fprintf(stderr, "getphdr() failed: %s\n", elf_errmsg(-1));
			exit(EXIT_FAILURE);
		}

		if (dbg) {
		printf("  Section %d:\n", i);
		printf("    %-20s 0x%jx\n", "p_offset", phdr.p_offset);
		printf("    %-20s 0x%jx\n", "p_vaddr",  phdr.p_vaddr);
		printf("    %-20s 0x%jx\n", "p_paddr",  phdr.p_paddr);
		printf("    %-20s 0x%jx\n", "p_filesz", phdr.p_filesz);
		printf("    %-20s 0x%jx\n", "p_memsz",  phdr.p_memsz);
		printf("    %-20s 0x%x [", "p_flags",  phdr.p_flags);

		if (phdr.p_flags & PF_X)	printf(" Execute");
		if (phdr.p_flags & PF_R)	printf(" Read");
		if (phdr.p_flags & PF_W)	printf(" Write");
		printf("]\n");

		printf("    %-20s 0x%jx\n", "p_align", phdr.p_align);
		}

		if (phdr.p_filesz == 0)
			continue;

		// Only create non-zero sized sections
		// A zero sized section is the mark of the end of the file.
		current_section++;

		r[i]->m_start = phdr.p_paddr;
		r[i]->m_len   = phdr.p_filesz;

		current_offset += phdr.p_memsz + sizeof(ELFSECTION);

		// Now, let's read in our section ...
		if (lseek(fd, phdr.p_offset, SEEK_SET) < 0) {
			fprintf(stderr, "Could not seek to file position %08lx\n", phdr.p_offset);
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		} if (phdr.p_filesz > phdr.p_memsz)
			phdr.p_filesz = 0;
		if (read(fd, r[i]->m_data, phdr.p_filesz) != (int)phdr.p_filesz) {
			fprintf(stderr, "Didnt read entire section\n");
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		}

		/*
		// Next, we need to byte swap it from big to little endian
		for(unsigned j=0; j<r[i]->m_len; j++)
			r[i]->m_data[j] = byteswap(r[i]->m_data[j]);
		*/

/*
		// Only turn this on if you need to, otherwise it creates
		// way too much debugging output--one line per char in the
		// design
		if (dbg) for(unsigned j=0; j<r[i]->m_len; j++)
			fprintf(stderr, "ADR[%04x -> %04x] = %02x\n",
				r[i]->m_start+j,
				(unsigned)(phdr.p_vaddr+j),
				r[i]->m_data[j] & 0x0ff);
*/
	}

	r[i] = (ELFSECTION *)(&d[current_offset]);
	r[current_section]->m_start = 0;
	r[current_section]->m_len   = 0;

	elf_end(e);
	close(fd);
}

