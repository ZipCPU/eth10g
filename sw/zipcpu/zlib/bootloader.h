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
