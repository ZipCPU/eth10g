////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/zipsw/zlib/bootloader.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	
//
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
#ifndef	BOOTLOADER_H
#define	BOOTLOADER_H

extern	int	_top_of_heap[1], _top_of_stack[1];
extern	int	_boot_address[1];

extern	int	_ram[1], _rom[1], _kram[1];

extern	int	_boot_address[1],
		_kram_start[1], _kram_end[1],
		_ram_image_start[1], _ram_image_end[1],
		_bss_image_end[1];

#endif
