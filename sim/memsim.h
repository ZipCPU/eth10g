////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	memsim.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This creates a memory like device to act on a WISHBONE bus.
//		It doesn't exercise the bus thoroughly, but does give some
//	exercise to the bus to see whether or not the bus master can control
//	it.
//
//	This particular version differs from the memsim version within the
//	ZipCPU project in that there is a variable delay from request to
//	completion.
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
#ifndef	MEMSIM_H
#define	MEMSIM_H

#include <stdint.h>

class	MEMSIM {
public:	
	typedef	unsigned int	BUSW;
	typedef	unsigned char	uchar;
	static const int	NWRDWIDTH;

	BUSW	*m_mem, m_len, m_mask, m_head, m_tail, m_delay_mask, m_delay;
	int	*m_fifo_ack;
	BUSW	*m_fifo_data;
	bool	m_cleared;

	MEMSIM(const unsigned int nwords, const unsigned int delay=27);
	~MEMSIM(void);
	void	load(const char *fname);
	void	load(const unsigned int addr, const char *buf,const size_t len);
	void	apply(const uchar wb_cyc, const uchar wb_stb,
				const uchar wb_we,
			const BUSW wb_addr, const uint32_t *wb_data,
				const uint64_t wb_sel,
			uchar &o_stall, uchar &o_ack, uint32_t *o_data);
	void	operator()(const uchar wb_cyc, const uchar wb_stb,
				const uchar wb_we,
			const BUSW wb_addr, const uint32_t *wb_data,
				const uint64_t wb_sel,
			uchar &o_stall, uchar &o_ack, uint32_t *o_data) {

		apply(wb_cyc, wb_stb, wb_we, wb_addr, wb_data, wb_sel,
			o_stall, o_ack, o_data);
	}
	BUSW &operator[](const BUSW addr) { return m_mem[addr&m_mask]; }
};

#endif
