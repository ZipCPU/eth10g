////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/emmcinfo.c
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
#include "board.h"
// #include "rxfns.h"
#include "txfns.h"
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <locale.h>
#include <zipcpu.h>
#include "ffconf.h"
#include "ff.h"
#include "diskiodrvr.h"

extern	int	emmc_boot(void *, unsigned, char *);
extern	int	emmc_altboot(void *, unsigned, char *);
extern	int	emmc_write_boot(void *, unsigned, char *);

#ifdef	NEED_MKFS
int	emmc_mkfs(void) {
	// {{{
	FRESULT	r;
	MKFS_PARM	fs_opt;
	char		*work_buffer;
	unsigned	work_len = 512*64;

	fs_opt.fmt = FM_FAT32;
	fs_opt.n_fat = 1;
	fs_opt.align = 3;	// log(units of sector sz),(2^3)*512=4kB
	fs_opt.n_root = 0;
	fs_opt.au_size = 0;
	work_buffer = (char *)malloc(work_len);
	//
	r = f_mkfs("2:", &fs_opt, work_buffer, work_len);
	free(work_buffer);
	work_buffer = NULL;

	if (r != FR_OK) {
		fprintf(stderr, "F_MKFS failed: %d\n", r);
	} else
		fprintf(stderr, "F_MKFS success!\n");
	return	r;
}
// }}}
#endif

int main(int argc, char **argv) {
	FATFS	vol;
	FRESULT	r;

	// Read the main directory
	DIR	ds;
	FILINFO	fis;

#ifdef	GPIO_TRACE_SET
	*_gpio = GPIO_TRACE_SET;
#endif

	// Mount our eMMC (disk) device
	// {{{
	r = f_mount(&vol, "2:/", 1);

#ifdef	NEED_MKFS
	if (0 && FR_NO_FILESYSTEM == r) {
		// {{{
		// Create a file system, if none exists.
		//	Disabled because ... we've already created a filesystem.
		r = emmc_mkfs();
		if (r != FR_OK) {
			goto failed;
		}

		r = f_mount(&vol, "2:/", 1);
		if (r != FR_OK) {
			fprintf(stderr, "F_MOUNT still failed: %d\n", r);
			goto failed;
		} else
			fprintf(stderr, "F-MOUNT Success\n");
		// }}}
	} else
#endif
	if (r != FR_OK) {
		fprintf(stderr, "ERR: Could not mount eMMC: %d\n", r);
		goto failed;
	}
	// }}}

	// Read the directory
	// {{{
	r = f_opendir(&ds, "2:/");
	if (r != FR_OK) {
		fprintf(stderr, "F_OPENDIR failed: %d\n", r);
			goto failed;
	}

	while(FR_OK == (r = f_readdir(&ds, &fis)) && (fis.fname[0] != '\0')) {
		printf("File: /%s%s\n", fis.fname,
			(fis.fattrib & AM_DIR) ? "/":"");
	} if (FR_OK != r) {
		fprintf(stderr, "F_READDIR failed: %d\n");
		goto failed;
	}
	// }}}

	// Write some boot data
	// {{{
	const	unsigned TSTLN = 8*512;
	char	*boot_data = malloc(TSTLN);
	void	*emmc_dev = NULL;

	// Find our "drive" device
	for(unsigned k=0; k < MAX_DRIVES; k++) {
		if (DRIVES[k].fd_addr == (void *)_emmc) {
			emmc_dev = DRIVES[k].fd_data;
		}
	}

	// Generate some pseudorandom data to test with
	for(unsigned k=0; k < TSTLN; k++) {
		unsigned	v = k >> 2;

		boot_data[k++] = (v >> 24) & 0x0ff;
		boot_data[k++] = (v >> 16) & 0x0ff;
		boot_data[k++] = (v >>  8) & 0x0ff;
		boot_data[k  ] =  v        & 0x0ff;
	}

	txstr("BOOT TEST DATA:\n");
	{
		unsigned	*sp = (unsigned *)boot_data;
		for(int k=0; k<8*512/4; k++) {
			printf("0x%08x ", *sp++);
			if (3 == (k&3))
				printf("\n");
			if (15 == (k & 15))
				printf("\n");
			if (127 == (k & 127))
				printf("\n");
		}
	}

	if (emmc_dev && boot_data) {
		emmc_write_boot(emmc_dev, TSTLN/512, boot_data);
	}
	// }}}

	// Test the boot data
	// {{{
	char	*test_buffer = malloc(TSTLN);

	{
		unsigned	*up = (unsigned *)test_buffer;
		for(int k=0; k<8*512/4; k++)
			*up++ = 0;
	}

	emmc_boot(emmc_dev, TSTLN/512, test_buffer);
	// emmc_altboot(emmc_dev, TSTLN/512, test_buffer);
	CLEAR_DCACHE;

	if (0 == memcmp(boot_data, test_buffer, TSTLN)) {
		printf("BOOT DATA TEST: Data matches\n");
	} else {
		unsigned	*up = (unsigned *)test_buffer;
		for(int k=0; k<8*512/4; k++) {
			printf("0x%08x ", *up++);
			if (3 == (k&3))
				printf("\n");
			if (15 == (k & 15))
				printf("\n");
			if (127 == (k & 127))
				printf("\n");
		}

		printf("BOOT DATA TEST: Data mismatch\n");
		goto failed;
	}

	// }}}
	// 
	printf("Success\n");
	return 0;

failed:
	fprintf(stderr, "EXIT on failures\n");
}
