////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/ttybus.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is the C++ program on the command side that will interact
//		with a UART on an FPGA, to command the WISHBONE on that same
//		FPGA to ... whatever we wish to command it to do.
//
//	This code does not run on an FPGA, is not a test bench, neither
//	is it a simulator.  It is a portion of a command program
//	for commanding an FPGA.
//
//	This particular implementation is a complete rewrite of the
//	last implementation, adding compression into the interface that
//	wasn't there before.
//
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
//
#ifndef	TTYBUS_H
#define	TTYBUS_H

#include "llcomms.h"
#include "devbus.h"

#define	RDBUFLN	2048
// }}}
class	TTYBUS : public DEVBUS {
public:
	unsigned long	m_total_nread;
private:
	LLCOMMSI	*m_dev;
	static	const	unsigned MAXRDLEN, MAXWRLEN;

	bool	m_interrupt_flag, m_decode_err, m_addr_set, m_bus_err;
	unsigned int	m_lastaddr;

	int	m_buflen, m_rdfirst, m_rdlast;
	char	*m_buf, *m_rdbuf;

	bool	m_wrloaded;
	int	m_rdaddr, m_wraddr;
	BUSW	m_readtbl[1024], m_writetbl[512];

	void	init(void) {
		m_total_nread = 0;
		m_interrupt_flag = false;
		m_buflen = 0; m_buf = NULL;
		m_addr_set = false;
		bufalloc(64);
		m_bus_err = false;
		m_decode_err = false;
		m_wrloaded = false;

		m_rdfirst = m_rdlast = 0;
		m_rdbuf = new char[RDBUFLN];

		m_rdaddr = m_wraddr = 0;
	}

	char	charenc(const int sixbitval) const;
	unsigned chardec(const char b) const;
	void	encode(const int fbits, const BUSW v, char *buf) const;
	unsigned decodestr(const char *buf) const;
	int	decodehex(const char hx) const;
	void	bufalloc(int len);
	BUSW	readword(void); // Reads a word value from the bus
	void	readv(const BUSW a, const int inc, const int len, BUSW *buf);
	void	writev(const BUSW a, const int p, const int len, const BUSW *buf);
	void	readidle(void);

	int	lclread(char *buf, int len);
	int	lclreadcode(char *buf, int len);
	char	*encode_address(const BUSW a);
	char	*readcmd(const int inc, const int len, char *buf);
public:
	TTYBUS(LLCOMMSI *comms) : m_dev(comms) { init(); }
	virtual	~TTYBUS(void) {
		m_dev->close();
		if (m_buf) { delete[] m_buf; m_buf = NULL; }
		delete m_rdbuf; m_rdbuf = NULL;
		delete	m_dev;
	}

	void	kill(void) { m_dev->close(); }
	void	close(void) {	m_dev->close(); }
	void	writeio(const BUSW a, const BUSW v);
	BUSW	readio(const BUSW a);
	void	readi( const BUSW a, const int len, BUSW *buf);
	void	readz( const BUSW a, const int len, BUSW *buf);
	void	writei(const BUSW a, const int len, const BUSW *buf);
	void	writez(const BUSW a, const int len, const BUSW *buf);
	bool	poll(void) { return m_interrupt_flag; };
	void	usleep(unsigned msec); // Sleep until interrupt
	void	wait(void); // Sleep until interrupt
	bool	bus_err(void) const { return m_bus_err; };
	void	reset_err(void) { m_bus_err = false; }
	void	clear(void) { m_interrupt_flag = false; }
};

#endif
