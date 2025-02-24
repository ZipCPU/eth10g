////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/zipelf.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	The ZIPELF class is designed to simplify the representation
// 		of the fields in an ELF file, for the purpose of loading a
// 	computer from the sections within it.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2025, Gisselquist Technology, LLC
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
#ifndef	ZIPELF_H
#define	ZIPELF_H

#include <stdint.h>

class	ELFSECTION {
public:
	uint32_t	m_start, m_len;
	char		m_data[4];
};

bool	iself(const char *fname);
void	elfread(const char *fname, uint32_t &entry, ELFSECTION **&sections);

#endif
