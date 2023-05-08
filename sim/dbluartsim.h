////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	dbluartsim.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To forward a Verilator simulated UART link, demultiplexed over
//		two adjacent TCP/IP pipe.
//
//	This file provides the description of the interface between the UARTSIM
//	and the rest of the world.  See below for more detailed descriptions.
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
#ifndef	DBLUARTSIM_H
#define	DBLUARTSIM_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <poll.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <signal.h>

#include "port.h"

#define	TXIDLE	0
#define	TXDATA	1
#define	RXIDLE	0
#define	RXDATA	1

#define	DBLPIPEBUFLEN	256

class	DBLUARTSIM	{
	bool	m_debug;

	int	setup_listener(const int port);
public:
	// The file descriptors:
	int	m_skt,	// Commands come in on this socket
		m_console, // Console port comes in/out on this socket
		m_cmd,	// Connection to the command port FD
		m_con;	// Connection to the console port FD
	char	m_conbuf[DBLPIPEBUFLEN],
		m_cmdbuf[DBLPIPEBUFLEN],
		m_rxbuf[DBLPIPEBUFLEN],
		m_cmdline[DBLPIPEBUFLEN],
		m_intransit_data;
	int	m_ilen, m_rxpos, m_cmdpos, m_conpos, m_cllen;
	bool	m_started_flag;
	bool	m_copy;
	//
	// The m_setup register is the 29'bit control register used within
	// the core.
	unsigned m_setup;
	// And the pieces of the setup register broken out.
	int	m_nparity, m_fixdp, m_evenp, m_nbits, m_nstop, m_baud_counts;
	// UART state
	int	m_rx_baudcounter, m_rx_state, m_rx_busy,
		m_rx_changectr, m_last_tx;
	int	m_tx_baudcounter, m_tx_state, m_tx_busy;
	unsigned	m_rx_data, m_tx_data;

	void	poll_accept(void);
	void	poll_read(void);
public:
	// The DBLUARTSIM constructor takes one argument: the base port on the
	// localhost to listen in on.  Once started, connections may be made
	// to this port to get the output from the port.
	DBLUARTSIM(const int port = FPGAPORT, const bool copy_to_stdout=true);
	// kill() closes any active connection and the socket.  Once killed,
	// no further output will be sent to the port.
	virtual	void	kill(void);

	// The operator() function is called on every tick.  The input is the
	// the output txuart transmit wire from the device.  The output is to
	// be connected to the the rxuart receive wire into the device.  This
	// makes hookup and operation very simple.
	//
	// This is the most appropriate simulation entry function if the 
	// setup register will never change.
	//
	int	operator()(int i_tx) {
		return tick(i_tx); }
	// If there is a possibility that the core might change the UART setup,
	// then it makes sense to include that current setup when calling the
	// tick operator.
	int	operator()(int i_tx, unsigned isetup) {
		setup(isetup); return tick(i_tx); }
	void	debug(const bool dbg) { m_debug = dbg; }
	// setup_listener is an attempt to encapsulate all of the network
	// related setup stuff.
	//
	// setup() busts out the bits from isetup to the various internal
	// parameters.  It is ideally only called between bits at appropriate
	// transition intervals. 
	void	setup(unsigned isetup);
	// We'll use the file descriptor for the listener socket to determine
	// whether we are connected to the network or not.  If not connected
	// to the network, then we assume m_conrd and m_conwr refer to 
	// your more traditional file descriptors, and use them as such.
	int	tick(const int i_tx);

	// Having just received a character, report it as received
	void	received(const char ch);
	//
	// Get the next character to transmit (if any)
	int	next(void);
};

#endif
