////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/fatfs/diskiodrvr.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generates a drives structure indicating the device address
//		and driver used for each mass storage device in the system.
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

#include <stddef.h>
#include <board.h>
#include <diskiodrvr.h>

DISKIODRVR	SDIODRVR  = {
	(DIO_INIT_FN)&sdio_init,
	(DIO_WRITE_FN)&sdio_write,
	(DIO_READ_FN)&sdio_read,
	(DIO_IOCTL_FN)&sdio_ioctl
};

DISKIODRVR	SDSPIDRVR = {
	(DIO_INIT_FN)&sdspi_init,
	(DIO_WRITE_FN)&sdspi_write,
	(DIO_READ_FN)&sdspi_read,
	(DIO_IOCTL_FN)&sdspi_ioctl
};

DISKIODRVR	EMMCDRVR  = {
	(DIO_INIT_FN)&emmc_init,
	(DIO_WRITE_FN)&emmc_write,
	(DIO_READ_FN)&emmc_read,
	(DIO_IOCTL_FN)&emmc_ioctl
};

// UPDATE ME!
// The following lines need to be updated from one board to the next, so that
// there's one FATDRIVE triplet per drive on the board, and so that MAX_DRIVES
// contains the number of items in the table.
//
FATDRIVE	DRIVES[MAX_DRIVES] = {
#ifdef	_BOARD_HAS_SDIO
		{ (void *)_sdio, &SDIODRVR, NULL },
#else
		{ NULL, NULL, NULL },
#endif
#ifdef	_BOARD_HAS_SDSPI
		{ (void *)_sdspi, &SDSPIDRVR, NULL },
#else
		{ NULL, NULL, NULL },
#endif
#ifdef	_BOARD_HAS_EMMC
		{ (void *)_emmc, &EMMCDRVR, NULL },
#else
		{ NULL, NULL, NULL },
#endif
#ifdef	_BOARD_HAS_CRUVMMC
		{ (void *)_cruvmmc, &EMMCDRVR, NULL },
#else
		{ NULL, NULL, NULL },
#endif
		{NULL, NULL, NULL }
	};
