////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/llcomms.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is the C++ program on the command side that will interact
//		with a UART on an FPGA, both sending and receiving characters.
//	Any bus interaction will call routines from this lower level library to
//	accomplish the actual connection to and transmission to/from the board.
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
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <termios.h>
#include <netinet/in.h>
#include <netdb.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <arpa/inet.h> 
#include <assert.h> 
#include <strings.h> 
#include <poll.h> 
#include <ctype.h> 

#include "llcomms.h"

const char LOCALHOSTSTR[] = "localhost";

LLCOMMSI::LLCOMMSI(void) {
	m_fdw = -1;
	m_fdr = -1;
	m_total_nread = 0l;
	m_total_nwrit = 0l;
}

void	LLCOMMSI::write(char *buf, int len) {
	int	nw;
	nw = ::write(m_fdw, buf, len);
	if (nw <= 0) {
		throw "Write-Failure";
	} else if (nw != len) {
		fprintf(stderr, "LLCOMMSI::ERR: %d byte write request, only %d written\n", len, nw);
		assert(nw == len);
	}
	m_total_nwrit += nw;
	assert(nw == len);
}

int	LLCOMMSI::read(char *buf, int len) {
	int	nr;
	nr = ::read(m_fdr, buf, len);
	if (nr <= 0) {
		throw "Read-Failure";
	}
	m_total_nread += nr;
	return nr;
}

void	LLCOMMSI::close(void) {
	if(m_fdw>=0)
		::close(m_fdw);
	if((m_fdr>=0)&&(m_fdr != m_fdw))
		::close(m_fdr);
	m_fdw = m_fdr = -1;
}

bool	LLCOMMSI::poll(unsigned ms) {
	struct	pollfd	fds;

	fds.fd = m_fdr;
	fds.events = POLLIN;
	::poll(&fds, 1, ms);

	if (fds.revents & POLLIN) {
		return true;
	} else return false;
}

int	LLCOMMSI::available(void) {
	return poll(0)?1:0;
}

TTYCOMMS::TTYCOMMS(const char *dev) {
	m_fdr = ::open(dev, O_RDWR | O_NONBLOCK);
	if (m_fdr < 0) {
		printf("\n Error : Could not open %s\n", dev);
		perror("O/S Err:");
		exit(-1);
	}

	if (isatty(m_fdr)) {
		struct termios tb;
		tcgetattr(m_fdr, &tb);
		cfmakeraw(&tb);
		// tb.c_iflag &= (~(IXON|IXOFF));
		tb.c_cflag &= (~(CRTSCTS));
		tcsetattr(m_fdr, TCSANOW, &tb);
		tcflow(m_fdr, TCOON);
	}

	m_fdw = m_fdr;
}

NETCOMMS::NETCOMMS(const char *host, const int port) {
	struct sockaddr_in serv_addr; 
	struct	hostent	*hp;
	const	char	*hostp = host;

	if ((m_fdr = socket(AF_INET, SOCK_STREAM, 0)) < 0) {
		printf("\n Error : Could not create socket \n");
		exit(-1);
	} 

	memset(&serv_addr, '0', sizeof(serv_addr)); 

	if (host == NULL || host[0] == '\0')
		hostp = LOCALHOSTSTR;
	else
		hostp = host;
	hp = gethostbyname(hostp);
	if (hp == NULL) {
		printf("Could not get host entity for %s\n", hostp);
		perror("O/S Err:");
		exit(-1);
	}
	bcopy(hp->h_addr, &serv_addr.sin_addr.s_addr, hp->h_length);

	serv_addr.sin_family = AF_INET;
	serv_addr.sin_port = htons(port); 

	if (connect(m_fdr,(struct sockaddr *)&serv_addr, sizeof(serv_addr))< 0){
		perror("Connect Failed Err");
		exit(-1);
	} 

	m_fdw = m_fdr;
}

void	NETCOMMS::close(void) {
	int	nr;
	char	buf[256];

	shutdown(m_fdw, SHUT_WR);
	while(1) {
		nr = ::read(m_fdr, buf, sizeof(buf));
		if (nr <= 0)
			break;
	}
	::close(m_fdw);
}
