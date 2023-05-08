////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/zipsw/zlib/umod.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is a temporary file--a crutch if you will--until a similar
//		capability is merged into GCC.  Right now, GCC has no way of
//	taking the module of two 64-bit numbers, and this routine provides that
//	capability.
//
//	This routine is required by and used by newlib's printf in order to
//	print decimal numbers (%d) to an IO stream.
//
//	Once gcc is properly patched, this will be removed from the 
//	repository.
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
#include <stdint.h>


unsigned long __udivdi3(unsigned long, unsigned long);

__attribute((noinline))
unsigned long __umoddi3(unsigned long a, unsigned long b) {
	unsigned long	r;

	// Return a modulo b, or a%b in C syntax
	r = __udivdi3(a, b);
	r = r * b;
	r = a - r;
	return r;
}

