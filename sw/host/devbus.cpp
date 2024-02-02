////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/devbus.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	The purpose of this file is to document an interface which
//		any device with a bus, whether it be implemented over a UART,
//	an ethernet, or a PCI express bus, must implement.  This describes
//	only an interface, and not how that interface is to be accomplished.
//
//	The neat part of this interface is that, if programs are designed to
//	work with it, than the implementation details may be changed later
//	and any program that once worked with the interface should be able
//	to continue to do so.  (i.e., switch from a UART controlled bus to a
//	PCI express controlled bus, with minimal change to the software of
//	interest.)
//
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
// }}}
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "port.h"
#include "regdefs.h"
#include "devbus.h"
// #include "netbus.h"
#include "ttybus.h"

DEVBUS	*connect_devbus(const char *ustr) {
	const char *str, *start = NULL;
	DEVBUS	*devbus = NULL;

	str = ustr;
	if (NULL == ustr || '\0' == ustr[0])
		str = getenv("FPGADEV");
	if (NULL == ustr || '\0' == ustr[0])
		str = strdup("SIM://localhost");
	if (NULL == str) {
		fprintf(stderr, "ERR: No device defined\n");
		exit(EXIT_FAILURE);
	}

	if (0==strncasecmp(str, "UART://", 7)) {
		start = &str[7];
	} else if (0==strncasecmp(str, "TTYBUS://", 9)) {
		start = &str[9];
	} else if (0==strncasecmp(str, "SIM://", 6)) {
		start = &str[6];
	} else {
		start = str;
	}

	char		*host, *ptr;
	unsigned	udp_port;

	host = strdup(start);
	ptr = strchr(host, ':');

	if (NULL == ptr && ptr[0] == '\0')
		udp_port = FPGAPORT;

	devbus = new TTYBUS(new NETCOMMS(host, udp_port));

	free(host);
	return devbus;
}

