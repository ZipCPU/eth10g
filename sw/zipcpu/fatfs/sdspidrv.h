////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sdcard.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Function header definitions and some constant definitions for
//		working with the SDSPI controller.  Other constant definitions
//	are currently provided by the AutoFPGA script and placed into board.h.
//	You can (currently) find alternate definitions for these in the
//	autotest_tb.cpp file.
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
#ifndef	SDSPIDRV_H
#define	SDSPIDRV_H

extern	int	sdcard_err;

struct	SDSPI_S;
struct	SDSPIDRV_S;

extern	struct SDSPIDRV_S *sdspi_init(struct SDSPI_S *);
extern	int	sdspi_read(struct SDSPIDRV_S *, unsigned sector, unsigned count, char *buf);
extern	int	sdspi_write(struct SDSPIDRV_S *, unsigned sector, unsigned count, const char *buf);
extern	int	sdspi_ioctl(struct SDSPIDRV_S *, char cmd, char *buf);

#endif	// SDSPIDRV_H
