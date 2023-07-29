////////////////////////////////////////////////////////////////////////////////
//
// Filename:	diskio.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This file contains the low-level SD-Card I/O wrappers for use
//		with the FAT-FS file-system library.  This low-level wrappers
//	are specific to systems having either an SDSPI or an SDIO device within
//	them.
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
#include "ff.h"
#include "diskio.h"
#include "board.h"
#include "sdspidrv.h"
#include "sdiodrv.h"
#include "diskiodrvr.h"

#define	STDIO_DEBUG
#include "zipcpu.h"

#ifdef	STDIO_DEBUG
  #include <stdio.h>
#endif

static inline	void	null(char *s,...) {}

DSTATUS	disk_status(
	BYTE pdrv
	) {
	// {{{
	unsigned	stat = 0;

	if (pdrv >= MAX_DRIVES || NULL == DRIVES[pdrv].fd_addr
			|| NULL == DRIVES[pdrv].fd_driver)
		return STA_NODISK;
	if (NULL == DRIVES[pdrv].fd_data)
		DRIVES[pdrv].fd_data= (DRIVES[pdrv].fd_driver->dio_init)(
					DRIVES[pdrv].fd_data);
	if (NULL == DRIVES[pdrv].fd_data
		|| RES_OK != (*DRIVES[pdrv].fd_driver->dio_ioctl)(
			DRIVES[pdrv].fd_data,
					MMC_GET_SDSTAT, (char *)&stat))
		stat = STA_NODISK;

	return	stat;
}
// }}}

DSTATUS	disk_initialize(
	BYTE pdrv
	) {
	// {{{
	if (pdrv >= MAX_DRIVES || NULL == DRIVES[pdrv].fd_addr
			|| NULL == DRIVES[pdrv].fd_driver)
		return STA_NODISK;
	else if (NULL != DRIVES[pdrv].fd_data
		|| NULL != (DRIVES[pdrv].fd_data
				= (*DRIVES[pdrv].fd_driver->dio_init)(
					DRIVES[pdrv].fd_addr))) {
		return RES_OK;
	} else
		return STA_NODISK;
}
// }}}

DRESULT disk_ioctl(
	BYTE pdrv,	// [IN] Drive number
	BYTE cmd,	// [IN] Control command code
	void *buff	// [I/O parameter and data buffer
	) {
	// {{{
	if (pdrv >= MAX_DRIVES || NULL == DRIVES[pdrv].fd_addr
			|| NULL == DRIVES[pdrv].fd_driver)
		return RES_ERROR;
	return (*DRIVES[pdrv].fd_driver->dio_ioctl)(DRIVES[pdrv].fd_data,
						cmd, buff);
}
// }}}

DWORD	get_fattime(void) {
	// {{{
	DWORD	result;
	unsigned	thedate, clocktime;

#ifdef	_BOARD_HAS_VERSION
	thedate   = *_version;
#else
	thedate = 0x20191001;
#endif
#ifdef	_BOARD_HAS_BUILDTIME
	clocktime = *_buildtime;
#else
	clocktime = 0x0; // Midnight
#endif

#ifdef	_BOARD_HAS_RTC
	clocktime = _rtc->r_clock;
#endif

	unsigned year, month, day, hrs, mns, sec;

	year =  ((thedate & 0xf0000000)>>28)*1000 +
		((thedate & 0x0f000000)>>24)*100 +
		((thedate & 0x00f00000)>>20)*10 +
		((thedate & 0x000f0000)>>16);
	year -= 1980;

	month = ((thedate & 0x00f000)>>12)*10 +
		((thedate & 0x000f00)>> 8);

	day   = ((thedate & 0x00f0)>> 4)*10 +
		((thedate & 0x000f)    );

	hrs   = ((clocktime & 0xf00000)>>20)*10 +
		((clocktime & 0x0f0000)>>16);

	mns   = ((clocktime & 0xf000)>>12)*10 +
		((clocktime & 0x0f00)>> 8);

	sec   = ((clocktime & 0xf0)>> 4)*10 +
		((clocktime & 0x0f));

	result = (sec & 0x01f) | ((mns & 0x3f)<<5)
		| ((hrs & 0x01f)<<11)
		| ((day & 0x01f)<<16)
		| ((month & 0x0f)<<21)
		| ((year & 0x0f)<<21);

	return result;
}
// }}}

DRESULT	disk_read(
	BYTE	pdrv,
	BYTE	*buff,
	DWORD	sector,
	UINT	count) {
	// {{{
	if (pdrv >= MAX_DRIVES || NULL == DRIVES[pdrv].fd_addr
			|| NULL == DRIVES[pdrv].fd_driver) {
		return RES_ERROR;
	}

#define	BROKEN
#ifdef	BROKEN
	return (*DRIVES[pdrv].fd_driver->dio_read)(DRIVES[pdrv].fd_data,
					sector, count, buff);
#else
	DWORD	res;
	res = (*DRIVES[pdrv].fd_driver->dio_read)(DRIVES[pdrv].fd_data,
					sector, count, buff);
	if (res != 0)
		asm("NOOP");
	return res;
#endif
}
// }}}

DRESULT	disk_write(
	BYTE		pdrv,
	const BYTE	*buff,
	DWORD		sector,
	UINT		count) {
	// {{{
	if (pdrv >= MAX_DRIVES || NULL == DRIVES[pdrv].fd_addr
			|| NULL == DRIVES[pdrv].fd_driver)
		return RES_ERROR;
	return (*DRIVES[pdrv].fd_driver->dio_write)(DRIVES[pdrv].fd_data,
					sector, count, buff);
}
