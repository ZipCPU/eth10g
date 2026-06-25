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

int main(int argc, char **argv) {
	FATFS	vol;
	FRESULT	r;

	// Read the main directory
	DIR	ds;
	FILINFO	fis;

#ifdef	GPIO_TRACE_SET
	*_gpio = GPIO_TRACE_SET;
#endif
	r = f_mount(&vol, "2:/", 1);
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
	} else if (r != FR_OK) {
		fprintf(stderr, "ERR: Could not mount eMMC: %d\n", r);
		goto failed;
	}

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

	printf("Success\n");
	return 0;

failed:
	fprintf(stderr, "EXIT on failures\n");
}
