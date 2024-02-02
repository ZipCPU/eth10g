////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/flashdrvr.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Flash driver.  Encapsulates writing, both erasing sectors and
//		the programming pages, to the flash device.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
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
//
// }}}
#ifndef	FLASHDRVR_H
#define	FLASHDRVR_H

#include "regdefs.h"

class	FLASHDRVR {
private:
	DEVBUS	*m_fpga;
	bool	m_debug;
	unsigned	m_id; // ID of the flash device

	//
	void	take_offline(void);
	void	place_online(void);
	void	restore_dualio(void);
	void	restore_quadio(void);
	static void restore_dualio(DEVBUS *fpga);
	static void restore_quadio(DEVBUS *fpga);
	//
	bool	verify_config(void);
	void	set_config(void);
	void	flwait(void);
public:
	FLASHDRVR(DEVBUS *fpga);
	bool	erase_sector(const unsigned sector, const bool verify_erase=true);
	bool	page_program(const unsigned addr, const unsigned len,
			const char *data, const bool verify_write=true);
	bool	write(const unsigned addr, const unsigned len,
			const char *data, const bool verify=false);

	unsigned	flashid(void);

	static void take_offline(DEVBUS *fpga);
	static void place_online(DEVBUS *fpga);
};

#endif
