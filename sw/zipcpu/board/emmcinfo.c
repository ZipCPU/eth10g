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
#include <zipsys.h>
#include "ffconf.h"
#include "ff.h"
#include "diskiodrvr.h"

extern	int	emmc_read(void *, unsigned, unsigned, char *);
extern	int	emmc_boot(void *, unsigned, char *);
extern	int	emmc_altboot(void *, unsigned, char *);
extern	int	emmc_write_boot(void *, unsigned, char *);

#define	STEP(F,T)	asm volatile("LSR 1,%0\n\tXOR.C %1,%0":"+r"(F):"r"(T))

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
	const	char	FILNAME[] = "2:/testfil.bin";
	FATFS	vol;
	FRESULT	r;

	// Read the main directory
	DIR	ds;
	FILINFO	fis;
	unsigned	seed, k, res, nw, nr;
	FIL	fp;
	const	unsigned	TESTLN = 1024*128 * 16;
	const	unsigned	INVERSION = 0x2523573,
				TAPS = 0xd0804001;
	char		*src_buffer = malloc(TESTLN), *test_buffer;
	unsigned	write_start, write_over,
			read_start, read_over, *s, *d;


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

	// Generate a "Seed" for subsequent random number generation
	// {{{
	seed = 15;
#ifdef	PWRCOUNT_ACCESS
	seed ^= *_pwrcount;
	if (0 == seed)
		seed++;
#endif
	// }}}

	// Use this seed to generate some random data
	// {{{
	{
		unsigned	*u = (unsigned *)&src_buffer[0], fill;
		fill = seed;
		for(k=0; k<TESTLN/4; k++) {
			STEP(fill, TAPS);
			u[k] = fill ^ INVERSION;
		}
	}
	// }}}

	printf("Write test\n"
		"------------------------------\n");
	// printf("OPEN:\n");
	// {{{
	res = f_open(&fp, FILNAME, FA_WRITE | FA_CREATE_ALWAYS);
	if (FR_OK != res) {
		if (res == FR_DISK_ERR) {
			printf("----> ERR!  Underlying DISK ERR\n");
		} else if (res == FR_NOT_READY) {
			printf("----> ERR!  Device not ready\n");
		} else if (res == FR_NO_FILE) {
			printf("----> ERR!  File not found\n");
		} else
			printf("----> ERR!  FOPEN failed, result = %d\n", res);
		goto failed;
	}
	// }}}

	// printf("WRITE:\n");
	// {{{
	nw =0;
	write_start = _zip->z_jiffies;
	res = f_write(&fp, src_buffer, TESTLN, &nw);
	write_over = _zip->z_jiffies;
	if (res != FR_OK) {
		printf("----> ERR!  Write result = %d\n", res);
		printf("TEST FAIL!\n");
	} else if (nw != TESTLN) {
		printf("----> ERR!  Only %d of %d bytes written\n", nw, TESTLN);
		printf("TEST FAIL!\n");
	}
	// }}}

	// printf("CLOSE:\n");
	// {{{
	res = f_close(&fp);
	if (res != FR_OK) {
		printf("----> ERR!  Close result = %d\n", res);
		goto failed;
	}
	// }}}

	// printf("SRC-DUMP:\n");
	// {{{
	/*
	// Dump the first and last sectors
	for(int k=0; k<512; k++) {
		printf("%02x ", src_buffer[k]& 0x0ff);
		if (15 == (k & 0x0f))
			printf("\n");
		else if (7 == (k & 0x0f))
			printf(" ");
	} printf("\n");

	for(int k=0; k<512; k++) {
		printf("%02x ", src_buffer[TESTLN-512+k]& 0x0ff);
		if (15 == (k & 0x0f))
			printf("\n");
		else if (7 == (k & 0x0f))
			printf(" ");
	}
	*/
	// }}}

	// Write Time report
	// {{{
	{
		unsigned write_time = write_over - write_start;
		double	write_sec = write_time * 10e-9;
		double	write_rate = TESTLN / write_sec / 1e3;

		printf("  Write transfer time: %8.6f s (0x%08x clocks)\n", write_sec, write_time);
		printf("  Write transfer rate: %7.1f kB/s\n", write_rate);
	}
	// }}}

	// Get access to the raw "drive" device
	// {{{
	void	*emmc_dev = NULL;

	// Find our "drive" device
	for(unsigned k=0; k < MAX_DRIVES; k++) {
		if (DRIVES[k].fd_addr == (void *)_emmc) {
			emmc_dev = DRIVES[k].fd_data;
		}
	}
	// }}}

	printf("Read test\n"
		"------------------------------\n");
	// Prep memory
	// {{{
	test_buffer = malloc(TESTLN);
	d = (unsigned *)test_buffer;
	if (NULL == test_buffer) {
		printf("PANIC!\n");
		printf("test_buffer = %08x\n", (unsigned)d);
		zip_halt();
	}

	// Pre-clear the memory
	for(k=0; k<TESTLN/4; k++)
		d[k] = 0;
	// }}}

	// printf("OPEN:\n");
	// {{{
	res = f_open(&fp, FILNAME, FA_READ);
	if (FR_OK != res) {
		if (res == FR_DISK_ERR) {
			printf("----> ERR!  Underlying DISK err\n");
		} else if (res == FR_NOT_READY) {
			printf("----> ERR!  Device not ready\n");
		} else if (res == FR_NO_FILE) {
			printf("----> ERR!  File not found\n");
		} else
			printf("----> ERR!  FOPEN failed, result = %d\n", res);
		printf("TEST FAIL!\n");
		goto failed;
	}
	// }}}

	// printf("READ:\n");
	// {{{
	nr = 0;
	read_start = _zip->z_jiffies;
	res = f_read(&fp, d, TESTLN, &nr);
	read_over = _zip->z_jiffies;
	if (FR_OK != res) {
		if (res == FR_DISK_ERR) {
			printf("----> ERR!  Underlying DISK err\n");
		} else if (res == FR_NOT_READY) {
			printf("----> ERR!  Device not ready\n");
		} else if (res == FR_NO_FILE) {
			printf("----> ERR!  File not found\n");
		} else
			printf("----> ERR!  Read result = %d\n", res);
		printf("TEST FAIL!\n");
		goto failed;
	} else if (nr != TESTLN) {
		printf("----> ERR!  Only %d of %d bytes read\n",
			nr, TESTLN);
		printf("TEST FAIL\n");
		goto failed;
	}
	// }}}
	// printf("CLOSE:\n");
	// {{{
	res = f_close(&fp);
	if (res != FR_OK) {
		printf("----> ERR!  Close result = %d\n", res);
		goto failed;
	}
	// }}}

	// Read Time report
	// {{{
	{
		unsigned	read_time = read_over - read_start;
		double	read_sec = (read_time * 10e-9);
		double	read_rate = TESTLN / read_sec / 1e3;
		printf("  Read  transfer time: %8.6f s (0x%08x clocks)\n", read_sec, read_time);
		printf("  Read  transfer rate: %7.1f kB/s\n", read_rate);
	}
	// }}}

	// printf("DST-DUMP:\n");
	// {{{
	/*
	// Dump the first and last sectors read
	for(int k=0; k<512; k++) {
		printf("%02x ", test_buffer[k]& 0x0ff);
		if (15 == (k & 0x0f))
			printf("\n");
		else if (7 == (k & 0x0f))
			printf(" ");
	} printf("\n");

	for(int k=0; k<512; k++) {
		printf("%02x ", test_buffer[TESTLN-512+k]& 0x0ff);
		if (15 == (k & 0x0f))
			printf("\n");
		else if (7 == (k & 0x0f))
			printf(" ");
	}
	*/
	// }}}

	printf("Verifying data\n"
		"------------------------------\n");
	// {{{
	{
		unsigned	*u = (unsigned *)&src_buffer[0], fill;
		fill = seed;

		int	fail_flag = 0;
		for(k=0; k<TESTLN/4; k++) {
			STEP(fill, TAPS);
			if (d[k] !=  (fill^INVERSION)) {
				printf("ERR!  PRN[%3d] = %08x doesn\'t match"
					" SD[%3d] = %08x (s[k] = 0x%08x)\n",
					k, fill^INVERSION, k, d[k],
					u[k]);
				fail_flag = 1;
			}
		} if (fail_flag) {
			goto failed;
		} printf("  (Passes)\n");
	}
	// }}}

// #define	BOOT_TEST
#ifdef	BOOT_TEST
	// Write some boot data
	// {{{
	const	unsigned BOOTLN = 8*512;
	char	*boot_data = malloc(BOOTLN);

	// Generate some pseudorandom data to test with
	for(unsigned k=0; k < BOOTLN; k++) {
		unsigned	v = k >> 2;

		boot_data[k++] = (v >> 24) & 0x0ff;
		boot_data[k++] = (v >> 16) & 0x0ff;
		boot_data[k++] = (v >>  8) & 0x0ff;
		boot_data[k  ] =  v        & 0x0ff;
	}

	if (0) {
		unsigned	*sp = (unsigned *)boot_data;

		txstr("BOOT TEST DATA:\n");
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
		emmc_write_boot(emmc_dev, BOOTLN/512, boot_data);
	}
	// }}}

	// Test the boot data
	// {{{
	{
		unsigned	*up = (unsigned *)test_buffer;
		for(int k=0; k<8*512/4; k++)
			*up++ = 0;
	}

	emmc_boot(emmc_dev, BOOTLN/512, test_buffer);
	// emmc_altboot(emmc_dev, BOOTLN/512, test_buffer);
	CLEAR_DCACHE;

	if (0 == memcmp(boot_data, test_buffer, BOOTLN)) {
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
#endif

	printf("Success\n");
	return 0;

failed:
	fprintf(stderr, "EXIT on failures\n");
}
