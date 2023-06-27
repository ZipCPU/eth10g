////////////////////////////////////////////////////////////////////////////////
//
// Filename:	diskio.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This file contains the low-level SD-Card I/O wrappers for use
//		with the FAT-FS file-system library.  This low-level wrappers
//	are specific to systems having only a single SDSPI device within them.
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
#include "sdcard.h"

#define	STDIO_DEBUG
#include "zipcpu.h"

#ifdef	STDIO_DEBUG
#include <stdio.h>
#define	DBGPRINTF	printf
#else
#define	DBGPRINTF	null
#endif

static inline	void	null(char *s,...) {}

int	gbl_csd_valid = 0;
char	gbl_csd_reg[128];
unsigned long	gbl_card_size = 0;
unsigned int	gbl_sector_size = 0;
unsigned int	gbl_erase_sector_size = 0;
unsigned int	card_initialized=0;

DSTATUS	disk_status(BYTE pdrv) {
	unsigned	stat = 0, card_ctrl = 0;

	if (pdrv != 0)
		stat = STA_NODISK | STA_NOINIT;
	else {
		card_ctrl = _sdcard->sd_ctrl;
		if (card_ctrl & SDSPI_PRESENTN)
			stat =	STA_NODISK | STA_NOINIT;
		else if (card_ctrl & SDSPI_REMOVED)
			stat = STA_NOINIT;
	}

	if (!card_initialized)
		stat |= STA_NOINIT;

	return stat;
}

DSTATUS	disk_initialize(
	BYTE pdrv
	)
{
	DSTATUS	dstat;
	gbl_csd_valid = 0;

	dstat = disk_status(pdrv);
	if (dstat & STA_NODISK)
		return STA_NODISK;

	if (dstat & STA_NOINIT) {
		int	r;
		r = sdcard_init();
		if (0 != r)
			return FR_DISK_ERR;
	}

	if (0 == sdcard_read_csd(gbl_csd_reg)) {
		gbl_csd_valid = 1;
// #define	INVALID_CSD_CID
#ifdef	INVALID_CSD_CID
#warning "This should come from the SD Card"
gbl_sector_size = 512;
gbl_erase_sector_size = 512;
gbl_card_size = 64 << 20;
#else
		if (0x00 == (gbl_csd_reg[0] & 0xc0)) {
			//
			// Standard capacity card, CSD v1
			//
			unsigned	C_SIZE, C_SIZE_MULT, READ_BL_LEN,
					BLOCK_LEN, BLOCKNR, SECTOR_SIZE,
					WRITE_BL_LEN;

			C_SIZE  =  gbl_csd_reg[6] & 0x0ff;
			C_SIZE |= (gbl_csd_reg[7] & 0x0ff) | (C_SIZE << 8);
			C_SIZE |= (gbl_csd_reg[8] & 0x0ff) | (C_SIZE << 8);

			C_SIZE >>= 6;
			C_SIZE &= 0x0fff;

			C_SIZE_MULT  = (gbl_csd_reg[ 9]& 0x0ff);
			C_SIZE_MULT |= (gbl_csd_reg[10]& 0x0ff) | (C_SIZE_MULT << 8);

			C_SIZE_MULT >>= 7;
			C_SIZE_MULT &= 0x07;

			READ_BL_LEN = (gbl_csd_reg[ 6]& 0x0ff);
			READ_BL_LEN = READ_BL_LEN & 0x0f;

			BLOCK_LEN = (1ul<<(READ_BL_LEN));
			gbl_sector_size = BLOCK_LEN;
			BLOCKNR  = (C_SIZE+1ul) * (1ul << (C_SIZE_MULT+2));
			gbl_card_size = BLOCKNR * BLOCK_LEN;

			// Get the size of an erasable sector
			SECTOR_SIZE  = (gbl_csd_reg[10]& 0x0ff);
			SECTOR_SIZE |= (gbl_csd_reg[11]& 0x0ff) | (SECTOR_SIZE << 8);
			SECTOR_SIZE >>= 7;
			SECTOR_SIZE &= 0x07f;


			WRITE_BL_LEN  = (gbl_csd_reg[12]& 0x0ff);
			WRITE_BL_LEN |= (gbl_csd_reg[13]& 0x0ff) | (SECTOR_SIZE << 8);
			WRITE_BL_LEN >>= 6;
			WRITE_BL_LEN &= 0x0f;
#ifdef	STDIO_DEBUG
DBGPRINTF("LO:\n"
"  C_SIZE_MULT  = %6d\n"
"  C_SIZE       = %6d\n"
"  READ_BL_LEN  = %6d\n"
"  SECTOR_SIZE  = %6d\n"
"  WRITE_BL_LEN = %6d\n",
		C_SIZE_MULT, C_SIZE, READ_BL_LEN, SECTOR_SIZE, WRITE_BL_LEN);
#endif

			gbl_erase_sector_size = (SECTOR_SIZE + 2)*WRITE_BL_LEN;
		} else if (0x40 == (gbl_csd_reg[0] & 0xc0)) {
			//
			// High capacity and extended capacity cards, CSD v2
			//
			unsigned	C_SIZE, READ_BL_LEN,
					BLOCK_LEN, BLOCKNR;

			READ_BL_LEN = 9;

			BLOCK_LEN = (1 << (READ_BL_LEN));

			gbl_sector_size = 512;
			C_SIZE = (gbl_csd_reg[7]& 0x0ff);
			C_SIZE = (gbl_csd_reg[8]& 0x0ff) | (C_SIZE << 8);
			C_SIZE = (gbl_csd_reg[9]& 0x0ff) | (C_SIZE << 8);
			C_SIZE = 0x03fffff;

#ifdef	STDIO_DEBUG
DBGPRINTF("HS: C_SIZE = %d\n", C_SIZE);
DBGPRINTF("  From ... %02x%02x%02x\n", gbl_csd_reg[7]&0x0ff,
		gbl_csd_reg[8]&0x0ff, gbl_csd_reg[9]&0x0ff);
#endif
			gbl_card_size = (C_SIZE+1ul) * BLOCK_LEN;
#ifdef	STDIO_DEBUG
DBGPRINTF("  Card Size = %lu\n", gbl_card_size);
#endif

			gbl_erase_sector_size = 65536;
		} else {
#ifdef	STDIO_DEBUG
			DBGPRINTF("Unrecognizable CSD: %02x %02x %02x ...\n",
				gbl_csd_reg[0] & 0x0ff,
				gbl_csd_reg[1] & 0x0ff,
				gbl_csd_reg[2] & 0x0ff);
#endif	// STDIO_DEBUG
		}
#endif // VALID_CSD_CID

		dstat &= ~STA_NOINIT;
	}
	return dstat;
}

DRESULT disk_ioctl(
	BYTE pdrv,	// [IN] Drive number
	BYTE cmd,	// [IN] Control command code
	void *buff	// [I/O parameter and data buffer
	) {
	DSTATUS	dstat;

	dstat = disk_status(pdrv);
	if (dstat & STA_NODISK)
		return RES_ERROR;
	else if (dstat && STA_NOINIT)
		return RES_NOTRDY;

	switch(cmd) {
	case CTRL_SYNC: {
			while(_sdcard->sd_ctrl & SDSPI_BUSY)
				;
			return	RES_OK;
		} break;
	case GET_SECTOR_COUNT:
		{	DWORD	*w = (DWORD *)buff;
			*w = (gbl_card_size / gbl_sector_size);
			return RES_OK;
		} break;
		break;
	case GET_SECTOR_SIZE:
		{	WORD	*w = (WORD *)buff;
			*w = gbl_sector_size;
			return RES_OK;
		} break;
	case GET_BLOCK_SIZE:
		{	DWORD	*w = (DWORD *)buff;
			*w = (gbl_erase_sector_size / gbl_sector_size);
			return RES_OK;
		} break;
	}

	return	RES_PARERR;
}

DWORD	get_fattime(void) {
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

DRESULT	disk_read(
	BYTE	pdrv,
	BYTE	*buff,
	DWORD	sector,
	UINT	count) {

#ifdef	STDIO_DEBUG
	DBGPRINTF("Disk:READ(%d,0x%x,%u)\n", pdrv, sector, count);
#endif
	if ((pdrv != 0)||(gbl_sector_size != 512))
		return RES_ERROR;

	for(unsigned k=0; k<count; k++) {
		char	*sector_ptr = buff + (k*gbl_sector_size);

		if (0 != sdcard_read(sector+k, sector_ptr)) {
#ifdef	STDIO_DEBUG
			DBGPRINTF("Disk:READ: READ ERR\n");
#endif
			return RES_ERROR;
		}
		/*
		// Dump any sector read
		printf("Successfully read sector %d\n", sector+k);
		for(unsigned b=0; b<512; b++) {
			printf("%02x ", sector_ptr[b]&0x0ff);
			if ((b & 15)==15)
				printf("\n");
		}
		*/
	}

	return RES_OK;
}

DRESULT	disk_write(
	BYTE		pdrv,
	const BYTE	*buff,
	DWORD		sector,
	UINT		count) {

#ifdef	STDIO_DEBUG
	DBGPRINTF("Disk:WRITE(%d,0x%x,%u)\n", pdrv, sector, count);
#endif
	if ((pdrv != 0)||(gbl_sector_size != 512))
		return RES_ERROR;

	for(unsigned k=0; k<count; k++) {
		const char	*sector_ptr = buff + (k*gbl_sector_size);

		if (0 != sdcard_write(sector+k, sector_ptr)) {
#ifdef	STDIO_DEBUG
			DBGPRINTF("Disk:WRITE: WRITE ERR, sector %d of %d, at sector #0x%08x\n", k+1, count, sector+k);
#endif
			if (0 != sdcard_write(sector+k, sector_ptr)) {
#ifdef	STDIO_DEBUG
				DBGPRINTF("Disk:WRITE: Double write fail--abort\n");
#endif
				return RES_ERROR;
			}
		}
	}

	return RES_OK;
}
