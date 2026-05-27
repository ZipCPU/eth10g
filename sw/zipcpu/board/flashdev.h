////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/flashdev.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Flash driver (header).  The flash drive attempts to
//		encapsulates the erasing and programming (i.e. writing)
//	necessary to set the values in a flash device.
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
// }}}
#ifndef	FLASHDEV_H
#define	FLASHDEV_H

extern	unsigned fl_flashid(void);
extern	void	fl_take_offline(void);
extern	void	fl_place_online(void);
extern	void	fl_restore_quadio(void);
extern	void	flwait(void);
extern	int	fl_erase_sector(const unsigned sector, const int verify_erase);
extern	int	fl_page_program(const unsigned addr, const unsigned len,
		const char *data, const int verify_write);

extern	int	fl_write(const unsigned addr, const unsigned len,
		const char *data, const int verify);
#endif
