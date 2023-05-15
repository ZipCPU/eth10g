////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbregs.cpp
// {{{
// Project:	Demonstration SONAR project
//
// Purpose:	To give a user access, via a command line program, to read
//		and write wishbone registers one at a time.  Thus this program
//	implements readio() and writeio() but nothing more.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022, Symbiotic EDA, Gmbh
// {{{
// This file is part of the demonstration SONAR project.  The demonstration
// SONAR project is proprietary to Symbiotic EDA, Gmbh.  It may not be
// redistributed without the express permission of an authorized representative
// of Symbiotic EDA, Gmbh.
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "regdefs.h"
#include "port.h"
#include "ttybus.h"
// #include "hexbus.h"

typedef	TTYBUS FPGA;

FPGA	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

bool	isvalue(const char *v) {
	const char *ptr = v;

	while(isspace(*ptr))
		ptr++;

	if ((*ptr == '+')||(*ptr == '-'))
		ptr++;
	if (*ptr == '+')
		ptr++;
	if (*ptr == '0') {
		ptr++;
		if (tolower(*ptr) == 'x')
			ptr++;
	}

	return (isdigit(*ptr));
}

void	usage(void) {
	printf("USAGE: wbregs [-d] address [value]\n"
"\n"
"\tWBREGS stands for Wishbone registers.  It is designed to allow a\n"
"\tuser to peek and poke at registers within a given FPGA design, so\n"
"\tlong as those registers have addresses on the wishbone bus.  The\n"
"\taddress may reference peripherals or memory, depending upon how the\n"
"\tbus is configured.\n"
"\n"
"\t-d\tIf given, specifies the value returned should be in decimal,\n"
"\t\trather than hexadecimal.\n"
"\n"
"\t-n [host]\tAttempt to connect, via TCP/IP, to host named [host].\n"
"\t\tThe default host is \'%s\'\n"
"\n"
"\t-p [port]\tAttempt to connect, via TCP/IP, to port number [port].\n"
"\t\tThe default port is \'%d\'\n"
"\n"
"\tAddress is either a 32-bit value with the syntax of strtoul, or a\n"
"\tregister name.  Register names can be found in regdefs.cpp\n"
"\n"
"\tIf a value is given, that value will be written to the indicated\n"
"\taddress, otherwise the result from reading the address will be \n"
"\twritten to the screen.\n", FPGAHOST, FPGAPORT);
}

int main(int argc, char **argv) {
	int	skp=0;
	bool	use_decimal = false;
	const char *host = FPGAHOST;
	int	port=FPGAPORT;

	skp=1;
	for(int argn=0; argn<argc-skp; argn++) {
		if (argv[argn+skp][0] == '-') {
			if (argv[argn+skp][1] == 'd') {
				use_decimal = true;
			} else if (argv[argn+skp][1] == 'n') {
				if (argn+skp+1 >= argc) {
					fprintf(stderr, "ERR: No network host given\n");
					exit(EXIT_SUCCESS);
				}
				host = argv[argn+skp+1];
				skp++; argn--;
			} else if (argv[argn+skp][1] == 'p') {
				if (argn+skp+1 >= argc) {
					fprintf(stderr, "ERR: No network port # given\n");
					exit(EXIT_SUCCESS);
				}
				port = strtoul(argv[argn+skp+1], NULL, 0);
				skp++; argn--;
			} else {
				usage();
				exit(EXIT_SUCCESS);
			}
			skp++; argn--;
		} else
			argv[argn] = argv[argn+skp];
	} argc -= skp;

	m_fpga = new FPGA(new NETCOMMS(host, port));

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	if ((argc < 1)||(argc > 2)) {
		// usage();
		printf("USAGE: wbregs address [value]\n");
		exit(-1);
	}

	const char *nm = NULL, *named_address = argv[0];
	unsigned address, value;

	if (isvalue(named_address)) {
		address = strtoul(named_address, NULL, 0);
		nm = addrname(address);
	} else {
		address = addrdecode(named_address);
		nm = addrname(address);
	}

	if (NULL == nm)
		nm = "";

	if (argc < 2) {
		FPGA::BUSW	v;
		try {
			unsigned char a, b, c, d;
			v = m_fpga->readio(address);
			a = (v>>24)&0x0ff;
			b = (v>>16)&0x0ff;
			c = (v>> 8)&0x0ff;
			d = (v    )&0x0ff;
			if (use_decimal)
				printf("%d\n", v);
			else
			printf("%08x (%8s) : [%c%c%c%c] %08x\n", address, nm, 
				isgraph(a)?a:'.', isgraph(b)?b:'.',
				isgraph(c)?c:'.', isgraph(d)?d:'.', v);
		} catch(BUSERR b) {
			printf("%08x (%8s) : BUS-ERROR\n", address, nm);
		} catch(const char *er) {
			printf("Caught bug: %s\n", er);
			exit(EXIT_FAILURE);
		}
	} else {
		try {
			value = strtoul(argv[1], NULL, 0);
			m_fpga->writeio(address, value);
			printf("%08x (%8s)-> %08x\n", address, nm, value);
		} catch(BUSERR b) {
			printf("%08x (%8s) : BUS-ERR)R\n", address, nm);
			exit(EXIT_FAILURE);
		} catch(const char *er) {
			printf("Caught bug on write: %s\n", er);
			exit(EXIT_FAILURE);
		}
	}

	if (m_fpga->poll())
		printf("FPGA was interrupted\n");
	delete	m_fpga;
}

