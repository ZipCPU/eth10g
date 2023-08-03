////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdiosim.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	
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
#ifndef	SDIOSIM_H
#define	SDIOSIM_H
#include <stdint.h>
#include <stdio.h>

class	SDIOSIM {
	FILE		*m_fp;
	uint32_t	m_buf[512/sizeof(uint32_t)];
	bool		m_readonly, m_reply_active, m_open_drain, m_ddr,
			m_data_started, m_cmd_started;
	uint32_t	m_last_dat, m_last_cmd, m_lastck, m_app_cmd,
			m_selected, m_RCA, m_width, m_drive;
	char		m_cmd_buf[8], m_cid[16], m_reply_buf[20],
			m_dbuf[512+1+32], m_csd[16];
	uint32_t	m_cmd_pos, m_reply_posn, m_reply_count, m_R1,
			m_reply_delay, m_sector, m_data_delay, m_data_posn;
protected:
	void		init(void);
	unsigned	cmdbit(unsigned);
	unsigned	datp(unsigned);
	unsigned	datn(unsigned);
	void		accept_command(void);
	void		load_reply(int cmd, unsigned arg);
	uint8_t		cmdcrc(int ln, char *buf);
	unsigned	blockcrc(unsigned fill, unsigned bit);
	void		CID(void);
	void		CSD(void);
	void		SCR(void);
public:
	// SDIOSIM(const unsigned lglen);
	SDIOSIM(const char *fname);
	void	load(const unsigned addr, const char *fname);
	void	load(const char *fname) { load(0, fname); }
	void	apply(unsigned sdclk, unsigned ddr,
			unsigned cmd_en, unsigned cmd_data,
			unsigned data_en, unsigned rx_en, unsigned tx_data,
			unsigned &o_sync, unsigned &async_sync,
			unsigned &async_data);
};

#endif
