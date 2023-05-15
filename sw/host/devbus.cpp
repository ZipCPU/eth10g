////////////////////////////////////////////////////////////////////////////////
//
// Filename:	devbus.cpp
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

