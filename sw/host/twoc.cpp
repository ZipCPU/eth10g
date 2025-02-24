////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/twoc.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Some various two's complement related C++ helper routines.
//		Specifically, these help extract signed numbers from
//		packed bitfields, while guaranteeing that the upper bits
//		are properly sign extended (or not) as desired.
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
//
#include "twoc.h"

long	sbits(const long val, const int bits) {
	long	r;

	r = val & ((1l<<bits)-1);
	if (r & (1l << (bits-1)))
		r |= (-1l << bits);
	return r;
}

bool	sfits(const long val, const int bits) {
	return (sbits(val, bits) == bits);
}

unsigned long	ubits(const long val, const int bits) {
	unsigned long r = val & ((1l<<bits)-1);
	return r;
}


