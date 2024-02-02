////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/flashsim.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This library simulates the operation of a Quad-SPI commanded
//		flash, such as the S25FL032P used on the Basys-3 development
//	board by Digilent.  As such, it is defined by 32 Mbits of memory
//	(4 Mbyte).
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
#ifndef	FLASHSIM_H
#define	FLASHSIM_H

#include "regdefs.h"

#ifndef	FLASH_NDUMMY
#define	FLASH_NDUMMY	10
#endif

#ifndef	FLASH_RDDELAY
#define	FLASH_RDDELAY	3
#endif

#define	QSPIF_WIP_FLAG			0x0001
#define	QSPIF_WEL_FLAG			0x0002
#define	QSPIF_DEEP_POWER_DOWN_FLAG	0x0200
class	FLASHSIM {
	typedef	enum {
		QSPIF_IDLE,
		QSPIF_QUAD_READ_IDLE,
		QSPIF_RDSR,
		QSPIF_RDCR,
		QSPIF_WRSR,
		QSPIF_CLSR,
		QSPIF_RDID,
		QSPIF_RELEASE,
		QSPIF_SLOW_READ,
		QSPIF_FAST_READ,
		QSPIF_QUAD_READ_CMD,
		QSPIF_QUAD_READ,
		QSPIF_SECTOR_ERASE,
		QSPIF_PP,
		QSPIF_QPP,
		QSPIF_BULK_ERASE,
		QSPIF_DEEP_POWER_DOWN,
		// Dual SPI states
		QSPIF_DUAL_READ_IDLE,
		QSPIF_DUAL_READ_CMD,
		QSPIF_DUAL_READ,
		QSPIF_INVALID
	} QSPIF_STATE;

	typedef	enum {
		FM_SPI,
		FM_DSPI,
		FM_QSPI
	} FLASH_MODE;

	QSPIF_STATE	m_state;
	char		*m_mem, *m_pmem;
	int		m_last_sck;
	unsigned	m_write_count, m_ireg, m_oreg, m_sreg, m_addr,
			m_count, m_config, m_mode_byte, m_creg, m_membytes,
			m_memmask, m_cmd_addrlen;
	bool		m_debug, m_idle_throttle;
	FLASH_MODE	m_mode;

	const	unsigned	CKDELAY, RDDELAY, NDUMMY;

	int		*m_ckdelay, *m_rddelay;

public:
	FLASHSIM(const int lglen = 24, bool debug = false,
		const int rddelay = FLASH_RDDELAY,
		const int ndummy = FLASH_NDUMMY);
	void	load(const char *fname) { load(0, fname); }
	void	load(const unsigned addr, const char *fname);
	void	load(const uint32_t offset, const char *data, const uint32_t len);
	bool	write_protect(void) { return ((m_sreg & QSPIF_WEL_FLAG)==0); }
	bool	write_in_progress(void) { return ((m_sreg & QSPIF_WIP_FLAG)!=0); }
	bool	xip_mode(void) { return (QSPIF_QUAD_READ_IDLE == m_state); }
	bool	deep_sleep(bool newval);
	bool	deep_sleep(void) const;
	bool	dual_mode(void) { return (m_mode == FM_DSPI); }
	bool	quad_mode(void) { return (m_mode == FM_QSPI); }
	void	debug(const bool dbg) { m_debug = dbg; }
	bool	debug(void) const { return m_debug; }
	unsigned operator[](const int index) {
		unsigned char	*cptr = (unsigned char *)&m_mem[index<<2];
		unsigned	v;
		v = (*cptr++);
		v = (v<<8)|(*cptr++);
		v = (v<<8)|(*cptr++);
		v = (v<<8)|(*cptr);

		return v; }
	void set(const unsigned addr, const unsigned val) {
		unsigned char	*cptr = (unsigned char *)&m_mem[addr<<2];
		*cptr++ = (val>>24);
		*cptr++ = (val>>16);
		*cptr++ = (val>> 8);
		*cptr   = (val);
		return;}
	int	operator()(const int csn, const int sck, const int dat);

	// simtick applies various programmable delays to the inputs in 
	// order to determine the outputs.  It's primary purpose is to
	// support an ODDR based clock (and or other) components.
	int	simtick(const int csn, const int sck, const int dat,
			const int mode);
};

#endif
