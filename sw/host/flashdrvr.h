////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	flashdrvr.h
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
