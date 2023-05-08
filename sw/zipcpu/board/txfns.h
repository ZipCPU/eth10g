////////////////////////////////////////////////////////////////////////////////
//
// Filename:	txfns.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	These are some *very* simple UART routines, designed to support
//		a program before the C-library is up and running.  Once the
//	C-library is running on a device, it is anticipated that these routines
//	will no longer be needed or used--since they access the raw hardware
//	device(s).
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
#ifndef	TXFNS_H
#define	TXFNS_H

#include "board.h"

extern	void	txchr(char ch);
extern	void	txstr(const char *str);
extern	void	txhex(unsigned val);
extern	void	txdecimal(int val);

#endif
