////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/flashsim.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This library simulates the operation of a Quad-SPI commanded
//		flash, such as the S25FL032P used on the Basys-3 development
//	board by Digilent.
//
//	This simulator is useful for testing in a Verilator/C++ environment,
//	where this simulator can be used in place of actual hardware.
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
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>

#include "flashsim.h"

#ifndef	CLKRATE_HZ
// Default to a 100MHz clock
// Much higher and we might suffer from overflow
#define	CLKRATE_HZ	100000000
#endif

extern const unsigned DEVID;
const unsigned	DEVID = 0x01152340;
static	const unsigned
	DEVESD = 0x014,
	MICROSECONDS = ((CLKRATE_HZ + 1)/ 1000000),
	MILLISECONDS = ((CLKRATE_HZ + 1)/ 1000),
	SECONDS = CLKRATE_HZ,
	tW     =   50 * MICROSECONDS, // write config cycle time
	tBE    =   32 * SECONDS,
	tDP    =   10 * SECONDS,
	tRES   =   30 * SECONDS,
// Shall we artificially speed up this process?
	tPP    = 12 * MICROSECONDS,
	tSE    = 15 * MILLISECONDS;
// or keep it at the original speed
	// tPP    = 1200 * MICROSECONDS,
	// tSE    = 1500 * MILLISECONDS;

FLASHSIM::FLASHSIM(const int lglen, bool debug,
		const int rddelay, const int ndummy)
			: m_debug(debug), CKDELAY(0),
			RDDELAY(rddelay), NDUMMY(ndummy) {
	// {{{
	m_membytes = (1<<lglen);
	m_memmask = (m_membytes - 1);
	m_mem = new char[m_membytes];
	m_pmem = new char[256];
	m_state = QSPIF_IDLE;
	m_last_sck = 1;
	m_write_count = 0;
	m_ireg = m_oreg = 0;
	m_sreg = 0x01c;
	m_creg = 0x001;	// Iinitial creg on delivery
	m_mode = FM_SPI;
	m_mode_byte = 0;
	m_idle_throttle = false;

	memset(m_mem, 0x0ff, m_membytes);
}
// }}}

void	FLASHSIM::load(const unsigned addr, const char *fname) {
	// {{{
	FILE	*fp;
	size_t	len;
	int	nr = 0;

	if (addr >= m_membytes)
		return;
	// If not given, then length is from the given address until the end
	// of the flash memory
	len = m_membytes-addr;

	if (NULL != (fp = fopen(fname, "r"))) {
		nr = fread(&m_mem[addr], sizeof(char), len, fp);
		fclose(fp);
		if (nr == 0) {
			fprintf(stderr, "SPI-FLASH: Could not read %s\n", fname);
			perror("O/S Err:");
		}
	} else {
		fprintf(stderr, "SPI-FLASH: Could not open %s\n", fname);
		perror("O/S Err:");
	}

	for(unsigned i=nr+addr; i<m_membytes; i++)
		m_mem[i] = 0x0ff;

	if (m_debug && addr == 0 && nr > 16) {
		fprintf(stderr, "FLASH LOAD: ");
		for(unsigned i=0; i<16; i++)
			fprintf(stderr, "%02x ", m_mem[i]);
		fprintf(stderr, "\n");
	}
}
// }}}

void	FLASHSIM::load(const uint32_t offset, const char *data,
		const uint32_t len) {
	uint32_t	moff = (offset & (m_memmask));

	memcpy(&m_mem[moff], data, len);
}

bool	FLASHSIM::deep_sleep(void) const {

	return (m_sreg & QSPIF_DEEP_POWER_DOWN_FLAG);
} bool	FLASHSIM::deep_sleep(bool newval) {
	if (newval)
		m_sreg |= QSPIF_DEEP_POWER_DOWN_FLAG;
	else
		m_sreg &= ~QSPIF_DEEP_POWER_DOWN_FLAG;

	return deep_sleep();
}

#define	QOREG(A)	m_oreg = ((m_oreg & (~0x0ff))|((A)&0x0ff))

int	FLASHSIM::operator()(const int csn, const int sck, const int dat) {
	// Keep track of a timer to determine when page program and erase
	// cycles complete.

	if (m_write_count > 0) {
		if (0 == (--m_write_count)) {// When done with erase/page pgm,
			m_sreg &= 0x0fc; // Clear the write in progress bit
			if (m_debug) printf("Write complete, clearing WIP (inside SIM)\n");
		} else if ((m_debug)&&((m_write_count & 0x03ffff)==0))
			printf("%6x cycles remaining \'til write/erase completion\n", m_write_count);
	}

	if (csn) {
		// {{{
		m_last_sck = 1;
		m_ireg = 0; m_oreg = 0;
		m_count= 0;

		if ((QSPIF_PP == m_state)||(QSPIF_QPP == m_state)) {
			// Start a page program
			if (m_debug) printf("FLASHSIM: Page Program write cycle begins (Addr = %08x)\n", (m_addr&(~0x0ff)));
			if (m_debug) printf("CK = %d & 7 = %d\n", m_count, m_count & 0x07);
			if (m_debug) printf("FLASHSIM: pmem = %08lx\n", (unsigned long)m_pmem);
			m_write_count = tPP;
			m_state = QSPIF_IDLE;
			m_sreg &= (~QSPIF_WEL_FLAG);
			m_sreg |= (QSPIF_WIP_FLAG);
			for(int i=0; i<256; i++) {
				/*
				if (m_debug) printf("%02x: m_mem[%02x] = %02x &= %02x = %02x\n",
					i, (m_addr&(~0x0ff))+i,
					m_mem[(m_addr&(~0x0ff))+i]&0x0ff, m_pmem[i]&0x0ff,
					m_mem[(m_addr&(~0x0ff))+i]& m_pmem[i]&0x0ff);
				*/
				m_mem[(m_addr&(~0x0ff))+i] &= m_pmem[i];
			}
			m_mode = FM_SPI;
		} else if (m_state == QSPIF_SECTOR_ERASE) {
			if (m_debug) printf("FLASHSIM: Actually Erasing sector, from %08x\n", m_addr);
			m_write_count = tSE;
			m_state = QSPIF_IDLE;
			m_sreg &= (~QSPIF_WEL_FLAG);
			m_sreg |= (QSPIF_WIP_FLAG);
			m_addr &= (-1<<16);
			for(int i=0; i<(1<<16); i++)
				m_mem[m_addr + i] = 0x0ff;
			if (m_debug) printf("FLASHSIM: Now waiting %d ticks delay\n", m_write_count);
		} else if (QSPIF_WRSR == m_state) {
			if (m_debug) printf("FLASHSIM: Actually writing status register\n");
			m_write_count = tW;
			m_state  = QSPIF_IDLE;
			m_sreg  &= (~QSPIF_WEL_FLAG);
			m_sreg  |= (QSPIF_WIP_FLAG);
		} else if (QSPIF_CLSR == m_state) {
			if (m_debug) printf("FLASHSIM: Actually clearing the status register bits\n");
			m_state = QSPIF_IDLE;
			m_sreg &= 0x09f;
		} else if (m_state == QSPIF_BULK_ERASE) {
			m_write_count = tBE;
			m_state = QSPIF_IDLE;
			m_sreg &= (~QSPIF_WEL_FLAG);
			m_sreg |= (QSPIF_WIP_FLAG);
			for(unsigned i=0; i<m_membytes; i++)
				m_mem[i] = 0x0ff;
		} else if (m_state == QSPIF_DEEP_POWER_DOWN) {
			m_write_count = tDP;
			m_state = QSPIF_IDLE;
		} else if (m_state == QSPIF_RELEASE) {
			m_write_count = tRES;
			m_state = QSPIF_IDLE;
		} else if (m_state == QSPIF_QUAD_READ_CMD) {
			if ((m_mode_byte & 0x0f0)!=0x0a0)
				m_mode = FM_SPI;
			else
				m_state = QSPIF_QUAD_READ_IDLE;
		} else if (m_state == QSPIF_DUAL_READ_CMD) {
			if ((m_mode_byte & 0x0f0)!=0x0a0)
				m_mode = FM_SPI;
			else
				m_state = QSPIF_DUAL_READ_IDLE;
		} else if (m_state == QSPIF_QUAD_READ) {
			if ((m_mode_byte & 0x0f0)!=0x0a0)
				m_mode = FM_SPI;
			else
				m_state = QSPIF_QUAD_READ_IDLE;
		} else if (m_state == QSPIF_DUAL_READ) {
			if ((m_mode_byte & 0x0f0)!=0x0a0)
				m_mode = FM_SPI;
			else
				m_state = QSPIF_DUAL_READ_IDLE;
		} else if (m_state == QSPIF_DUAL_READ_IDLE) {
		} else if (m_state == QSPIF_QUAD_READ_IDLE) {
		}

		m_oreg = 0x0fe;
		return dat;
		// }}}
	} else if ((!m_last_sck)||(sck == m_last_sck)) {
		// {{{
		// Only change on the falling clock edge
		// printf("SFLASH-SKIP, CLK=%d -> %d\n", m_last_sck, sck);
		m_last_sck = sck;
		if (m_mode == FM_QSPI)
			return (m_oreg>>8)&0x0f;
		else if (m_mode == FM_DSPI)
			return ((m_oreg>>8)&0x03)|(dat & 0x0c);
		else
			return ((m_oreg & 0x0100)?2:0) | (dat & 0x0d);
		// }}}
	}

	// Shift in new data
	// {{{
	// We'll only get here if ...
	//	last_sck = 1, and sck = 0, thus transitioning on the
	//	negative edge as with everything else in this interface
	if (m_mode == FM_QSPI) {
		m_ireg   = (m_ireg << 4) | (dat & 0x0f);
		m_count += 4;
		m_oreg <<= 4;
	} else if (m_mode == FM_DSPI) {
		m_ireg   = (m_ireg << 2) | (dat & 0x03);
		m_count += 2;
		m_oreg <<= 2;
	} else {
		m_ireg = (m_ireg << 1) | (dat & 1);
		m_count++;
		m_oreg <<= 1;
	}
	// }}}

	// printf("PROCESS, COUNT = %d, IREG = %02x\n", m_count, m_ireg);
	if (m_state == QSPIF_QUAD_READ_IDLE) {
		// {{{
		// Cannot be in this state and deep power down
		assert((m_sreg & QSPIF_DEEP_POWER_DOWN_FLAG)==0);

		assert(quad_mode());
		if (m_count == m_cmd_addrlen) {
			if (m_debug) printf("FLASHSIM: Entering from Quad-Read Idle to Quad-Read\n");
			if (m_debug) printf("FLASHSIM: QI/O Idle Addr = %02x\n", m_ireg&0x0ffffff);
			m_addr = (m_ireg) & m_memmask;
			assert((m_addr & (~(m_memmask)))==0);
			m_state = QSPIF_QUAD_READ;
		} m_oreg = 0;
		// }}}
	} else if (m_state == QSPIF_DUAL_READ_IDLE) {
		// {{{
		// Cannot be in this state and deep power down
		assert((m_sreg & QSPIF_DEEP_POWER_DOWN_FLAG)==0);

		assert(dual_mode());
		if (m_count == m_cmd_addrlen) {
			if (m_debug) printf("DSPI: Entering from Dual-Read Idle to Dual-Read\n");
			if (m_debug) printf("DSPI: DI/O Idle Addr = %02x\n", m_ireg&0x0ffffff);
			m_addr = (m_ireg) & m_memmask;
			assert((m_addr & (~(m_memmask)))==0);
			m_state = QSPIF_DUAL_READ;
		} m_oreg = 0;
		// }}}
	} else if (m_count == 8) {
		// {{{
		QOREG(0x0a5);
		m_cmd_addrlen = 24;
		// printf("SFLASH-CMD = %02x\n", m_ireg & 0x0ff);
		// Figure out what command we've been given
		if (m_debug) printf("SPI FLASH CMD %02x\n", m_ireg&0x0ff);
		if ((m_sreg & QSPIF_DEEP_POWER_DOWN_FLAG)&&((m_ireg & 0x0ff) != 0xab)) {
			if (m_debug) {
				printf("Design is in deep power down.  Flash command ignored\n");
			}
		} else switch(m_ireg & 0x0ff) {
		case 0x01: // Write status register
			if (2 !=(m_sreg & 0x203)) {
				if (m_debug) printf("FLASHSIM: WEL not set, cannot write status reg\n");
				m_state = QSPIF_INVALID;
			} else
				m_state = QSPIF_WRSR;
			break;
		case 0x02: // Page program
			// {{{
			if (2 != (m_sreg & 0x203)) {
				if (m_debug) printf("FLASHSIM: Cannot program at this time, SREG = %x\n", m_sreg);
				m_state = QSPIF_INVALID;
			} else {
				m_state = QSPIF_PP;
				if (m_debug) printf("PAGE-PROGRAM COMMAND ACCEPTED\n");
				m_cmd_addrlen = 24;
			}
			break;
			// }}}
		case 0x03: // Read data bytes
			// {{{
			if (m_debug) printf("FLASHSIM: SLOW-READ (single-bit)\n");
			m_state = QSPIF_SLOW_READ;
			m_cmd_addrlen = 24;
			break;
			// }}}
		case 0x04: // Write disable
			m_state = QSPIF_IDLE;
			m_sreg &= (~QSPIF_WEL_FLAG);
			break;
		case 0x05: // Read status register
			m_state = QSPIF_RDSR;
			if (m_debug) printf("FLASHSIM: READING STATUS REGISTER: %02x\n", m_sreg);
			QOREG(m_sreg);
			break;
		case 0x06: // Write enable
			m_state = QSPIF_IDLE;
			m_sreg |= QSPIF_WEL_FLAG;
			if (m_debug) printf("FLASHSIM: WRITE-ENABLE COMMAND ACCEPTED\n");
			break;
		case 0x0b: // Here's the read that we support
			if (m_debug) printf("FLASHSIM: FAST-READ (single-bit)\n");
			m_state = QSPIF_FAST_READ;
			break;
		case 0x12: // Page program
			// {{{
			if (2 != (m_sreg & 0x203)) {
				if (m_debug) printf("FLASHSIM: Cannot program at this time, SREG = %x\n", m_sreg);
				m_state = QSPIF_INVALID;
			} else {
				m_state = QSPIF_PP;
				if (m_debug) printf("PAGE-PROGRAM COMMAND ACCEPTED\n");
				m_cmd_addrlen = 32;
			}
			break;
			// }}}
		case 0x13: // Read data bytes, 32b address
			// {{{
			if (m_debug) printf("FLASHSIM: SLOW-READ (single-bit)\n");
			m_state = QSPIF_SLOW_READ;
			m_cmd_addrlen = 32;
			break;
			// }}}
		case 0x30:
			if (m_debug) printf("FLASHSIM: CLEAR STATUS REGISTER COMMAND\n");
			m_state = QSPIF_CLSR;
			break;
		case 0x32: // QUAD Page program, 4 bits at a time
			// {{{
			if (2 != (m_sreg & 0x203)) {
				if (m_debug) printf("FLASHSIM: Cannot program at this time, SREG = %x\n", m_sreg);
				m_state = QSPIF_INVALID;
			} else {
				m_state = QSPIF_QPP;
				if (m_debug) printf("FLASHSIM: QUAD-PAGE-PROGRAM COMMAND ACCEPTED\n");
				if (m_debug) printf("FLASHSIM: pmem = %08lx\n", (unsigned long)m_pmem);
				m_cmd_addrlen = 24;
			}
			break;
			// }}}
		case 0x34: // QUAD Page program, 4 bits at a time
			// {{{
			if (2 != (m_sreg & 0x203)) {
				if (m_debug) printf("FLASHSIM: Cannot program at this time, SREG = %x\n", m_sreg);
				m_state = QSPIF_INVALID;
			} else {
				m_state = QSPIF_QPP;
				if (m_debug) printf("FLASHSIM: QUAD-PAGE-PROGRAM COMMAND ACCEPTED\n");
				if (m_debug) printf("FLASHSIM: pmem = %08lx\n", (unsigned long)m_pmem);
				m_cmd_addrlen = 32;
			}
			break;
			// }}}
		case 0x35: // Read configuration register
			m_state = QSPIF_RDCR;
			if (m_debug) printf("FLASHSIM: READING CONFIGURATION REGISTER: %02x\n", m_creg);
			QOREG(m_creg);
			break;
		case 0x50: // Clear flag status register
			m_state = QSPIF_IDLE;
			if (m_debug) printf("FLASHSIM: CLEARING FLAG-STATUS REGISTER\n");
			// This is a NOOP command
			QOREG(0);
			break;
		case 0x61: // Write enhanced volatile configuration register
			m_state = QSPIF_IDLE;
			if (m_debug) printf("FLASHSIM: WRITING ENHANCED VOLATILE-CONFIGURATION-REG");
			// We'll treat this as a NOOP command--for now
			QOREG(0);
			break;
		case 0x70: // Read flag status register register
			m_state = QSPIF_IDLE;
			if (m_debug) printf("FLASHSIM: READING FLAG-STATUS REGISTER\n");
			QOREG(0);
			break;
		case 0x81: // Write enhanced configuration register
			QOREG(0);
			break;
		case 0x9f: // Read ID
			m_state = QSPIF_RDID;
			if (m_debug) printf("FLASHSIM: READING ID, %02x\n", (DEVID>>24)&0x0ff);
			QOREG((DEVID>>24)&0x0ff);
			break;
		case 0xab: // Release from DEEP POWER DOWN
			if (m_sreg & QSPIF_DEEP_POWER_DOWN_FLAG) {
				if (m_debug) printf("FLASHSIM: Release from deep power down\n");
				m_sreg &= (~QSPIF_DEEP_POWER_DOWN_FLAG);
				m_write_count = tRES;
			} m_state = QSPIF_RELEASE;
			break;
		case 0xb9: // DEEP POWER DOWN
			if (0 != (m_sreg & 0x01)) {
				if (m_debug) printf("FLASHSIM: Cannot enter DEEP POWER DOWN, in middle of write/erase\n");
				m_state = QSPIF_INVALID;
			} else {
				m_sreg  |= QSPIF_DEEP_POWER_DOWN_FLAG;
				m_state  = QSPIF_IDLE;
			}
			break;
		case 0xbb: // Fast Read Dual I/O
			// {{{
			// printf("QSPI: DUAL-I/O-READ\n");
			m_state = QSPIF_DUAL_READ_CMD;
			m_mode = FM_DSPI;
			m_cmd_addrlen = 24;
			break;
			// }}}
		case 0xc7: // Bulk Erase
			// {{{
			if (2 != (m_sreg & 0x203)) {
				if (m_debug) printf("FLASHSIM: WEL not set, cannot erase device\n");
				m_state = QSPIF_INVALID;
			} else
				m_state = QSPIF_BULK_ERASE;
			break;
			// }}}
		case 0xd8: // Sector Erase
			// {{{
			if (2 != (m_sreg & 0x203)) {
				if (m_debug) printf("FLASHSIM: WEL not set, cannot erase sector\n");
				m_state = QSPIF_INVALID;
			} else {
				m_state = QSPIF_SECTOR_ERASE;
				if (m_debug) printf("FLASHSIM: SECTOR_ERASE COMMAND\n");
				m_cmd_addrlen = 24;
			}
			break;
			// }}}
		case 0xdc: // Sector Erase, 32b address
			// {{{
			if (2 != (m_sreg & 0x203)) {
				if (m_debug) printf("FLASHSIM: WEL not set, cannot erase sector\n");
				m_state = QSPIF_INVALID;
			} else {
				m_state = QSPIF_SECTOR_ERASE;
				if (m_debug) printf("FLASHSIM: SECTOR_ERASE COMMAND\n");
				m_cmd_addrlen = 32;
			}
			break;
			// }}}
		case 0x0eb: // Here's the (other) read that we support
			// {{{
			// printf("QSPI: QUAD-I/O-READ\n");
			m_state = QSPIF_QUAD_READ_CMD;
			m_mode = FM_QSPI;
			m_cmd_addrlen = 24;
			break;
			// }}}
		case 0x0ec: // Same thing, but w/ 32b address
			// {{{
			// printf("QSPI: QUAD-I/O-READ (32b)\n");
			m_state = QSPIF_QUAD_READ_CMD;
			m_mode = FM_QSPI;
			m_cmd_addrlen = 32;
			break;
			// }}}
		case 0x000:	// Dummy implementation of CMD 8'h00
		case 0x031:	// Dummy implementation of CMD 8'h31
		case 0x0ff:	// Dummy implementation of CMD 8'hff
			m_state = QSPIF_IDLE;
			m_mode = FM_SPI;
			break;
		default:
			printf("FLASHSIM: UNRECOGNIZED SPI FLASH CMD: %02x\n", m_ireg&0x0ff);
			m_state = QSPIF_INVALID;
			assert(0 && "Unrecognized command\n");
			break;
		}
		// }}}
	} else if ((0 == (m_count&0x07))&&(m_count != 0)) {
		// {{{
		QOREG(0);
		if ((m_idle_throttle)&&(m_state != QSPIF_IDLE))
			m_idle_throttle = false;
		switch(m_state) {
		case QSPIF_IDLE:
			// {{{
			if ((m_debug)&&(!m_idle_throttle))
				printf("TOO MANY CLOCKS from QUAD-IDLE, SPIF in IDLE\n");
			m_idle_throttle = true;
			break;
			// }}}
		case QSPIF_WRSR:
			// {{{
			if (m_count == 16) {
				m_sreg = (m_sreg & 0x061) | (m_ireg & 0x09c);
				if (m_debug) printf("Request to set sreg to 0x%02x\n",
					m_ireg&0x0ff);
			} else if (m_count == 24) {
				m_creg = (m_creg & 0x0fd) | (m_ireg & 0x02);
				if (m_debug) printf("Request to set creg to 0x%02x\n",
					m_ireg&0x0ff);
			} else {
				fprintf(stderr, "FLASH-ERR: TOO MANY CLOCKS FOR WRR!!!\n");
				exit(EXIT_FAILURE);
				m_state = QSPIF_IDLE;
			} break;
			// }}}
		case QSPIF_CLSR:
			assert(0 && "Too many clocks for CLSR command!!\n");
			break;
		case QSPIF_RDID:
			// {{{
			/*
			if (m_count == 32) {
				m_addr = m_ireg & m_memmask;
				if (m_debug) printf("READID, ADDR = %08x\n", m_addr);
				QOREG((DEVID>>16));
				if (m_debug) printf("FLASHSIM: READING ID, %02x\n", (DEVID>>8)&0x0ff);
			} else if (m_count > 32) {
				QOREG((DEVID>>(16+8*(m_count-32)/8)));
				if (m_debug) printf("FLASHSIM: READING ID, %02x -- DONE\n", 0x00);
			} */
			QOREG((DEVID >> (32-m_count)));
			break;
			// }}}
		case QSPIF_RDSR:
			// {{{
			// printf("Read SREG = %02x, wait = %08x\n", m_sreg,
				// m_write_count);
			QOREG(m_sreg);
			break;
			// }}}
		case QSPIF_RDCR:
			// {{{
			if (m_debug) printf("Read CREG = %02x\n", m_creg);
			QOREG(m_creg);
			break;
			// }}}
		case QSPIF_SLOW_READ:
			// {{{
			if (m_count == (m_cmd_addrlen+8)) {
				m_addr = m_ireg & m_memmask;
				if (m_debug) printf("READ, ADDR = %08x\n", m_addr);
				assert((m_addr & (~(m_memmask)))==0);
				// if (m_debug) printf("MEM[%06x] = %02x\n",
				//	m_addr, m_mem[m_addr]&0x0ff);
				QOREG(m_mem[m_addr++]);
			} else if ((m_count >= (m_cmd_addrlen+16))&&(0 == (m_sreg&0x01))) {
				// if (m_debug) printf("MEM[%06x] = %02x\n",
				//	m_addr, m_mem[m_addr]&0x0ff);
				QOREG(m_mem[m_addr++]);
			} else m_oreg = 0;
			break;
			// }}}
		case QSPIF_FAST_READ:
			// {{{
			if (m_count == (m_cmd_addrlen+8)) {
				m_addr = m_ireg & m_memmask;
				if (m_debug) printf("FAST READ, ADDR = %08x\n", m_addr);
				QOREG(0x0c3);
				assert((m_addr & (~(m_memmask)))==0);
			} else if ((m_count >= m_cmd_addrlen+16)&&(0 == (m_sreg&0x01))) {
				//if (m_count == 40)
					//printf("DUMMY BYTE COMPLETE ...\n");
				QOREG(m_mem[m_addr++]);
				// if (m_debug) printf("SPIF[%08x] = %02x\n", m_addr-1, m_oreg);
			} else m_oreg = 0;
			break;
			// }}}
		case QSPIF_DUAL_READ_CMD:
			// {{{
			// The command to go into quad read mode took 8 bits
			// that changes the timings, else we'd use quad_Read
			// below
			if (m_count == (m_cmd_addrlen+8)) {
				m_addr = m_ireg & m_memmask;
				if (m_debug) printf("DSPI: DUAL READ, ADDR = %06x\n", m_addr);
				assert((m_addr & (~(m_memmask)))==0);

			} else if ((m_count == (m_cmd_addrlen+8)+8)&&(0 == (m_sreg&0x01))) {
				m_mode_byte = (m_ireg) & 0x0ff;
				if (m_debug) printf("DSPI: MODE BYTE = %02x\n", m_mode_byte);
				QOREG(m_mem[m_addr++]);
			} else if ((m_count > (m_cmd_addrlen+8)+8)&&(0 == (m_sreg&0x01))) {
				QOREG(m_mem[m_addr++]);
				if (m_debug) printf("FLASHSIMF[%08x]/DR = %02x\n",
					m_addr-1, m_oreg);
			} else m_oreg = 0;
			break;
			// }}}
		case QSPIF_QUAD_READ_CMD:
			// {{{
			// The command to go into quad read mode took 8 bits
			// that changes the timings, else we'd use quad_Read
			// below
			if (m_count == (m_cmd_addrlen + 8)) {
				m_addr = m_ireg & m_memmask;
				// printf("FAST READ, ADDR = %08x\n", m_addr);
				// printf("QSPI: QUAD READ, ADDR = %06x\n", m_addr);
				assert((m_addr & (~(m_memmask)))==0);
			} else if (m_count == (m_cmd_addrlen + 8)+8) {
				m_mode_byte = (m_ireg) & 0x0ff;
				if (m_debug) printf("QSPI: MODE BYTE = %02x\n", m_mode_byte);
			} else if ((m_count > (m_cmd_addrlen + 8)+4*NDUMMY)&&(0 == (m_sreg&0x01))) {
				QOREG(m_mem[m_addr++]);
				// printf("QSPIF[%08x]/QR = %02x\n",
					// m_addr-1, m_oreg);
			} else m_oreg = 0;
			break;
			// }}}
		case QSPIF_DUAL_READ:
			// {{{
			if (m_count == m_cmd_addrlen+8) {
				m_mode_byte = (m_ireg & 0x0ff);
				if (m_debug) printf("DSPI/DR: MODE BYTE = %02x\n", m_mode_byte);
			}
			QOREG(m_mem[m_addr++]);
			if (m_debug) printf("DSPIF[%08x]/DR = %02x\n", m_addr-1, m_oreg & 0x0ff);
			break;
			// }}}
		case QSPIF_QUAD_READ:
			// {{{
			if (m_count == m_cmd_addrlen+4*2) {
				m_mode_byte = (m_ireg & 0x0ff);
				if (m_debug) printf("QSPI/QR: MODE BYTE = %02x\n", m_mode_byte);
			} else if ((m_count >= m_cmd_addrlen+4*NDUMMY)&&(0 == (m_sreg&0x01))) {
				QOREG(m_mem[m_addr++]);
				if (m_debug) printf("QSPIF[%08x]/QR = %02x\n", m_addr-1, m_oreg & 0x0ff);

assert(m_addr != 0x06080);
			} else m_oreg = 0;
			break;
			// }}}
		case QSPIF_PP:
			// {{{
			if (m_count == m_cmd_addrlen+8) {
				m_addr = m_ireg & m_memmask;
				if (m_debug) printf("FLASHSIM: PAGE-PROGRAM ADDR = %06x\n", m_addr);
				assert((m_addr & (~(m_memmask)))==0);
				// m_page = m_addr >> 8;
				for(int i=0; i<256; i++)
					m_pmem[i] = 0x0ff;
			} else if (m_count >= m_cmd_addrlen+16) {
				m_pmem[m_addr & 0x0ff] = m_ireg & 0x0ff;
				// printf("QSPI: PMEM[%02x] = 0x%02x -> %02x\n", m_addr & 0x0ff, m_ireg & 0x0ff, (m_pmem[(m_addr & 0x0ff)]&0x0ff));
				m_addr = (m_addr & (~0x0ff)) | ((m_addr+1)&0x0ff);
			} break;
			// }}}
		case QSPIF_QPP:
			// {{{
			if (m_count == m_cmd_addrlen+8) {
				m_addr = m_ireg & m_memmask;
				m_mode = FM_QSPI;
				if (m_debug) printf("FLASHSIM/QR: PAGE-PROGRAM ADDR = %06x\n", m_addr);
				assert((m_addr & (~(m_memmask)))==0);
				// m_page = m_addr >> 8;
				for(int i=0; i<256; i++)
					m_pmem[i] = 0x0ff;
			} else if (m_count >= m_cmd_addrlen+16) {
				m_pmem[m_addr & 0x0ff] = m_ireg & 0x0ff;
				// printf("QSPI/QR: PMEM[%02x] = 0x%02x -> %02x\n", m_addr & 0x0ff, m_ireg & 0x0ff, (m_pmem[(m_addr & 0x0ff)]&0x0ff));
				m_addr = (m_addr & (~0x0ff)) | ((m_addr+1)&0x0ff);
			} break;
			// }}}
		case QSPIF_SECTOR_ERASE:
			// {{{
			if (m_count == m_cmd_addrlen+8) {
				m_addr = m_ireg & 0x0ffc000;
				if (m_debug) printf("SECTOR_ERASE ADDRESS = %08x\n", m_addr);
				assert((m_addr & 0xfc00000)==0);
			} break;
			// }}}
		case QSPIF_RELEASE:
			if (m_count >= m_cmd_addrlen+8) {
				QOREG(DEVESD);
			} break;
		default:
			break;
		}
		// }}}
	} // else printf("SFLASH->count = %d\n", m_count);

	m_last_sck = sck;
	if (m_mode == FM_QSPI)
		return (m_oreg>>8)&0x0f;
	else if (m_mode == FM_DSPI)
		return ((m_oreg>>8)&0x03)|(dat & 0x0c);
	else
		return ((m_oreg & 0x0100)?2:0)|(dat & 0x0d);
}

//
// simtick
//
// Simulate an ODDR clock.  Also, adjust the timing in case the clock and
// data are not aligned, or likewise in case the incoming data is not
// aligned with the clock tick upon which it is sent.
//
int	FLASHSIM::simtick(const int csn, const int sck, const int dat,
		const int mod) {
	const bool	ODDR_IO = false;
	int	lclsck;

	if ((CKDELAY > 0)&&(m_ckdelay == NULL)) {
		m_ckdelay = new int[CKDELAY+8];
		for(unsigned i=0; i<CKDELAY; i++)
			m_ckdelay[i] = 0;
	} if ((RDDELAY>0)&&(m_rddelay == NULL)) {
		m_rddelay = new int[RDDELAY];
	}

	if (CKDELAY > 0) {
		// Delay the incoming clock value by CKDELAY clocks
		lclsck = m_ckdelay[0];
		for(unsigned i=0; i+1<CKDELAY; i++)
			m_ckdelay[i] = m_ckdelay[i+1]&1;
		m_ckdelay[CKDELAY-1] = sck&1;
	} else
		lclsck = sck;

	// Simulate an ODDR for the clock
	int	r;
	if (ODDR_IO) {
		r = (*this)(csn, (lclsck != 0)?0:1, dat);
		r = (*this)(csn, 1, dat);
	} else
		r = (*this)(csn, lclsck, dat);

	if (false) {
		// Debug the transaction
		if (!csn) {
			printf("%s %s/%s %x -> %x",
				(csn)?"   ":"CSN", (sck)?"PCK":"   ",
				(lclsck)?"SCK":"   ", dat, r);
			switch(mod) {
			case 0: case 1:	printf(" (SPI)");	break;
			case 2:		printf(" (QDI)");	break;
			case 3:		printf(" (QDO)");	break;
			case 4:		printf(" (DDI)");	break;
			case 5:		printf(" (DDO)");	break;
			} printf(",%d",mod);

			if (m_ckdelay != NULL)
				printf(" -- %d %d", CKDELAY, m_ckdelay[0]);
			printf("\n");
		}
	}


	switch(mod) {
	case 0: case 1:	// Normal SPI transaction
		r &= 2;
		r |= (dat&1);
		r |= 0x0c;
		break;
	case 2:	// QSPI master driven
		r = dat;
		break;
	case 3:	// QSPI slave driven
		break;
	case 4:	// DSPI master driven
		r = dat & 3;
		r |= 0x0c;
		break;
	case 5:	// DSPI slave driven
		r &= 3;
		r |= 0x0c;
	}

	if (RDDELAY > 0) {
		int	lclr;

		// Delay the output by RDDELAY clocks
		lclr = m_rddelay[0];
		for(unsigned i=0; i<RDDELAY-1; i++)
			m_rddelay[i] = m_rddelay[i+1];
		m_rddelay[RDDELAY-1] = r;

		r = lclr & 0x0f;
	}

	return r;
}
