////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	twoc.cpp
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


