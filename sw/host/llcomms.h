////////////////////////////////////////////////////////////////////////////////
//
// Filename:	llcomms.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is the C++ program on the command side that will interact
//		with a UART on an FPGA, both sending and receiving characters.
//	Any bus interaction will call routines from this lower level library to
//	accomplish the actual connection to and transmission to/from the board.
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
#ifndef	LLCOMMS_H
#define	LLCOMMS_H

class	LLCOMMSI {
protected:
	int	m_fdw, m_fdr;
	LLCOMMSI(void);
public:
	unsigned long	m_total_nread, m_total_nwrit;

	virtual	~LLCOMMSI(void) { close(); }
	virtual	void	kill(void)  { this->close(); };
	virtual	void	close(void);
	virtual	void	write(char *buf, int len);
	virtual int	read(char *buf, int len);
	virtual	bool	poll(unsigned ms);

	// Tests whether or not bytes are available to be read, returns a 
	// count of the bytes that may be immediately read
	virtual	int	available(void); // { return 0; };
};

class	TTYCOMMS : public LLCOMMSI {
public:
	TTYCOMMS(const char *dev);
};

class	NETCOMMS : public LLCOMMSI {
public:
	NETCOMMS(const char *dev, const int port);
	virtual	void	close(void);
};

#endif
