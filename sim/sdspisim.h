////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdspisim.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This library simulates the operation of a SPI commanded SD-Card,
//		such as might be found on a XuLA2-LX25 board made by xess.com.
//
//	This simulator is for testing use in a Verilator/C++ environment, where
//	it would be used in place of the actual hardware.
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
#ifndef	SDSPISIM_H
#define	SDSPISIM_H

#include <stdint.h>

typedef enum	eRESET_STATES {
	SDSPI_POWERUP_RESET,
	SDSPI_CMD0_IDLE,
	SDSPI_RCVD_CMD8,
	SDSPI_RCVD_ACMD41,
	SDSPI_RESET_COMPLETE,
	SDSPI_IN_OPERATION
} RESET_STATES;

#define	SDSPI_RSPLEN	8
#define	SDSPI_MAXBLKLEN	(1+2048+2)
#define	SDSPI_CSDLEN	(16)
#define	SDSPI_CIDLEN	(16)
class	SDSPISIM {
	FILE		*m_dev;
	unsigned long	m_devblocks;

	int		m_last_sck, m_delay, m_mosi;
	bool		m_busy, m_debug, m_block_address, m_altcmd_flag,
			m_syncd, m_host_supports_high_capacity, m_reading_data,
			m_have_token;

	RESET_STATES	m_reset_state;

	int		m_cmdidx, m_bitpos, m_rspidx, m_rspdly, m_blkdly,
				m_blklen, m_blkidx, m_last_miso, m_powerup_busy;
	unsigned	m_rxloc;
	char		m_cmdbuf[8], m_dat_out, m_dat_in;
	char		m_rspbuf[SDSPI_RSPLEN];
	char		m_block_buf[SDSPI_MAXBLKLEN];
	uint8_t		m_csd[SDSPI_CSDLEN], m_cid[SDSPI_CIDLEN];

	void	CID(void);
	void	CSD(void);
	unsigned	read_bitfield(int, int, int, const uint8_t *);
public:
	SDSPISIM(const bool debug = false);
	void	load(const char *fname);
	void	debug(const bool dbg) { m_debug = dbg; }
	bool	debug(void) const { return m_debug; }
	int	operator()(const int csn, const int sck, const int dat);
	unsigned cmdcrc(int ln, char *buf) const;
	bool	check_cmdcrc(char *buf) const;
	unsigned blockcrc(int ln, char *buf) const;
	void	add_block_crc(int ln, char *buf) const;

	unsigned	OCR(void);
	uint8_t	CSD(int index);
	uint8_t	CID(int index);
};

#endif
