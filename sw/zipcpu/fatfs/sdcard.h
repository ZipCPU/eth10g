////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sdcard.h
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
#ifndef	SDCARD_H
#define	SDCARD_H

#include "board.h"

#define	SDERR_READ	0x001
#define	SDERR_WRITE	0x002
#define	SDERR_INIT	0x010

#define	SPEED_25MHZ	0x01
#define	SPEED_17MHZ	0x02
#define	SPEED_12MHZ	0x03
#define	SPEED_10MHZ	0x04
#define	SPEED_400KHZ	0x7c
#define	SPEED_200KHZ	0xf9
#define	SPEED_100KHZ	0x1f3
#define	SPEED_SLOW	SPEED_400KHZ
#define	SPEED_FAST	SPEED_25MHZ
// #define	SPEED_FAST	SPEED_17MHZ
// #define	SPEED_FAST	SPEED_400KHZ

#define	SECTOR_8B	0x030000	// Used by SCR register
#define	SECTOR_16B	0x040000	// CSD and CID registers
#define	SECTOR_512B	0x090000	// 512-byte disk sectors
//
//
// Book recommen ds sequence of: CMD0, (CMD8), CMD58, ACMD41(wait), CMD58
//	for startup
//

extern	int	sdcard_err;
extern	int	sdcard_ocr;
extern	char	sdcard_csd[16];
extern	char	sdcard_cid[16];

#ifdef	_BOARD_HAS_SDSPI

extern	int	sdcard_read_ocr(void);
extern	int	sdcard_read_scr(unsigned *scr);
extern	int	sdcard_read_csd(char *csd);
extern	int	sdcard_read_cid(char *cid);
extern	int	sdcard_init(void);
extern	int	sdcard_read(int sector, char *buf);
extern	int	sdcard_write(int sector, const char *buf);

#else
// _BOARD_HAS_SDSPI is defined by AutoFPGA when including the SDSPI controller
// into a design, according to the SDSPI script
#error "No _BOARD_HAS_SDSPI defined"
#endif	// _BOARD_HAS_SDSPI
#endif	// SDCARD_H
