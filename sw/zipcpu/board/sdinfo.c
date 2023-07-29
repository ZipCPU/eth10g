////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sdinfo.c
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
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
// }}}
//	http://www.apache.org/licenses/LICENSE-2.0
// {{{
// Unless required by applicable law or agreed to in writing, files
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
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

int main(int argc, char **argv) {
	int	nxt, ntyp, npc, nts, nbt;
	char	rxstr[150];
	const char DELIMITERS[] = ", \t";
	const char	*istr="11";
	FATFS	vol;
	FRESULT	r;

#ifdef	GPIO_SD_RESET_CLR
	*_gpio = GPIO_SD_RESET_CLR;
#endif
	r = f_mount(&vol, "/", 1);
	if (r != FR_OK)
		printf("Could not mount SD-Card: err %d\n", r);

	// Read the main directory
	DIR	ds;
	FILINFO	fis;

	r = f_opendir(&ds, "/");
	if (r != FR_OK) {
		fprintf(stderr, "F_OPENDIR failed: %d\n", r);
		goto failed;
	}

	do {
		r = f_readdir(&ds, &fis);
		if (r != FR_OK) {
			fprintf(stderr, "F_READDIR failed: %d\n");
			goto failed;
		} if (fis.fname[0] == 0) {
			// printf("End of list\n");
			break;
		}

		printf("File: /%s%s\n", fis.fname,
			(fis.fattrib & AM_DIR) ? "/":"");
	} while(1);

	printf("Success\n");
	return 0;

failed:
	fprintf(stderr, "EXIT on failures\n");
}
