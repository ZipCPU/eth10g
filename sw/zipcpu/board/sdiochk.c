////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/sdiochk.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Bring up the SDIO interface slowly, one command at a time,
//		examining any potential errors along the way.  This is to
//	verify that the SDIO hardware works as expected.
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
// }}}
#include "board.h"
// #include "rxfns.h"
#include "txfns.h"
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <locale.h>
#include <zipcpu.h>

typedef	struct SDIO_S {
	volatile uint32_t	sd_cmd, sd_data, sd_fifa, sd_fifb, sd_phy;
} SDIO;

#ifdef	_BOARD_HAS_SDIOSCOPE
// #define	SETSCOPE	_sdioscope->s_ctrl = 0x0400efff
// #define	TRIGGER		_sdioscope->s_ctrl = 0xff00efff
#define	SETSCOPE	_sdioscope->s_ctrl = 0x0400efff
#define	TRIGGER		_sdioscope->s_ctrl = 0xff00efff
#else
#define	SETSCOPE
#define	TRIGGER
#endif

const uint32_t
	SDIO_CMD	= 0x00000040,
	SDIO_RNONE	= 0x00000000,
	SDIO_R1		= 0x00000100,
	SDIO_ERR	= 0x00008000,
	SDIO_REMOVED	= 0x00040000;

#ifdef	_BOARD_HAS_SDIO
void	wait_while_busy(void) {
	unsigned	v;

	do {
		v = _sdio->sd_cmd;
	} while(v & 0x104800);
}
#endif

int main(int argc, char **argv) {
#ifndef	_BOARD_HAS_SDIO
	txstr("This board configuration does not have any SDIO hardware\r\n");
#else
	unsigned	rca;
	unsigned	cid[4];
	unsigned	csd[4];

	txstr("STARTUP\r\n");

	// Set up the PHY
	_sdio->sd_phy = 0x090000fc;	//  100kHz
	// _sdio->sd_phy = 0x0900007f;	//  200kHz
	// _sdio->sd_phy = 0x09000041;	//  400kHz
	// _sdio->sd_phy = 0x0900001b;	// 1MHz

	while(0x0fc != (_sdio->sd_phy & 0x0ff))
		;

	for(int i=0; i<1000000; i++) asm("NOOP");
	SETSCOPE;

	txstr("CMD0:    GO_IDLE\r\n");
	// {{{
	_sdio->sd_data = 0;
	_sdio->sd_cmd = SDIO_REMOVED | SDIO_CMD | SDIO_RNONE | SDIO_ERR;
	wait_while_busy();
	if ((_sdio->sd_cmd & 0x80ff) != SDIO_CMD) {
		TRIGGER;
		goto failed;
	}

	txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
	// }}}

	txstr("CMD8:    SEND_IF_COND (");
	txhex((SDIO_R1|SDIO_CMD)+8); txstr(")\r\n");
	// {{{
	_sdio->sd_data = 0x01a5;
	_sdio->sd_cmd  = (SDIO_R1 | SDIO_CMD) + 8;
	wait_while_busy();
	if ((_sdio->sd_cmd & 0x80ff) != 8) {
		TRIGGER;
		goto failed;
	}

	txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
	// }}}

	// SEND_OP_COND
	// {{{
	do {
		txstr("CMD55:   SEND_APP_CMD\r\n");
		_sdio->sd_data = 0;
		_sdio->sd_cmd  = (SDIO_ERR | SDIO_CMD | SDIO_R1) + 55;
		wait_while_busy();
		if ((_sdio->sd_cmd & 0x80ff) != 55) {
			TRIGGER;
			txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
				txstr("\r\n");
			goto failed;
		}

		txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
		txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");

		txstr("ACMD41:  SEND_OP_COND\r\n");
		_sdio->sd_data = 0x40ff8000;
		_sdio->sd_cmd  = (SDIO_CMD | SDIO_R1) + 41;
		wait_while_busy();
		if ((_sdio->sd_cmd & 0x00ff) != 0x03f) {
			TRIGGER;
			txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
				txstr("\r\n");
			goto failed;
		}

		txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
		txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
		_sdio->sd_cmd  = 0x8100;
		txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	} while(0 == (_sdio->sd_data & 0x80000000));

	if ((_sdio->sd_data & 0xbfffffff) != 0x80ff8000) {
		txstr("ERROR: SD-DATA = "); txhex(_sdio->sd_data);
			txstr("\r\n");
		TRIGGER;
		goto failed;
	}
	// }}}

	txstr("CMD2:    ALL_SEND_CID\r\n");
	// {{{
	_sdio->sd_data = 0x0;
	_sdio->sd_cmd  = 0x8242;
	wait_while_busy();
	if ((_sdio->sd_cmd & 0x0ff) != 0x3f) {
		TRIGGER;
		txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
			txstr("\r\n");
		goto failed;
	}

	txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
	txstr("  FIFA[0]: "); txhex(cid[0] = _sdio->sd_fifa); txstr("\r\n");
	txstr("  FIFA[1]: "); txhex(cid[1] = _sdio->sd_fifa); txstr("\r\n");
	txstr("  FIFA[2]: "); txhex(cid[2] = _sdio->sd_fifa); txstr("\r\n");
	txstr("  FIFA[3]: "); txhex(cid[3] = _sdio->sd_fifa); txstr("\r\n");

	if (cid[0] == 0 && cid[1] == 0) {
		TRIGGER;
		txstr("ERROR: No CID\r\n");
		goto failed;
	}
	// }}}

	txstr("CMD3:    SEND_RCA\r\n");
	// {{{
	_sdio->sd_data = 0x0;
	_sdio->sd_cmd  = 0x8143;
	wait_while_busy();
	if ((_sdio->sd_cmd & 0x81ff) != 0x0103) {
		txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
			txstr("\r\n");
		TRIGGER;
		goto failed;
	}

	txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	rca = _sdio->sd_data >> 16;
	txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
	txstr("  RCA:     "); txhex(rca); txstr("\r\n");
	// }}}

	_sdio->sd_phy = 0x09003003;	// 25MHz, push-pull
	// _sdio->sd_phy = 0x09003004;	// 12MHz, push-pull
	while(0x03 != (_sdio->sd_phy & 0x0ff))
		;

	// From this state, I should now be able to issue
	//	CMD4	(SET_DSR/RNONE)
	//	CMD9	(SEND_CSD/R2),
	//	CMD10	(SEND_CID/R2),
	//	CMD3	(SEND_RCA/R6), and
	//	CMD7 (SELECT_CARD)

	txstr("CMD10:   SEND_CID\r\n");
	// {{{
	_sdio->sd_data = rca << 16;
	_sdio->sd_cmd  = 0x824a;
	wait_while_busy();
	if ((_sdio->sd_cmd & 0x0ff) != 0x3f) {
		TRIGGER;
		txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
			txstr("\r\n");
		goto failed;
	}

	txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
	txstr("  FIFA[0]: "); txhex(cid[0] = _sdio->sd_fifa); txstr("\r\n");
	txstr("  FIFA[1]: "); txhex(cid[1] = _sdio->sd_fifa); txstr("\r\n");
	txstr("  FIFA[2]: "); txhex(cid[2] = _sdio->sd_fifa); txstr("\r\n");
	txstr("  FIFA[3]: "); txhex(cid[3] = _sdio->sd_fifa); txstr("\r\n");

	if (cid[0] == 0 && cid[1] == 0) {
		TRIGGER;
		txstr("ERROR: No CID\r\n");
		goto failed;
	}
	// }}}

	txstr("CMD9:    SEND_CSD\r\n");
	// {{{
	_sdio->sd_data = rca << 16;
	_sdio->sd_cmd  = 0x8249;
	wait_while_busy();
	if ((_sdio->sd_cmd & 0x0ff) != 0x3f) {
		TRIGGER;
		txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
			txstr("\r\n");
		goto failed;
	}

	txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
	txstr("  FIFA[0]: "); txhex(csd[0] = _sdio->sd_fifa); txstr("\r\n");
	txstr("  FIFA[1]: "); txhex(csd[1] = _sdio->sd_fifa); txstr("\r\n");
	txstr("  FIFA[2]: "); txhex(csd[2] = _sdio->sd_fifa); txstr("\r\n");
	txstr("  FIFA[3]: "); txhex(csd[3] = _sdio->sd_fifa); txstr("\r\n");

	if (csd[0] == 0 && csd[1] == 0) {
		TRIGGER;
		txstr("ERROR: No CSD\r\n");
		goto failed;
	}
	// }}}

	txstr("CMD7:    SELECT_CARD\r\n");
	// {{{
	_sdio->sd_data = rca << 16;
	txstr("  Predata: "); txhex(_sdio->sd_data); txstr("\r\n");
	_sdio->sd_cmd  = 0x8147;
	wait_while_busy();
	if ((_sdio->sd_cmd & 0x81ff) != 0x0107) {
		txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
			txstr("\r\n");
		TRIGGER;
		goto failed;
	}

	txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
	// }}}

	txstr("CMD55:   SEND_APP_CMD\r\n");
	// {{{
	_sdio->sd_data = rca << 16;
	_sdio->sd_cmd  = 0x8140 + 55;
	wait_while_busy();
	if ((_sdio->sd_cmd & 0x80ff) != 55) {
		txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
			txstr("\r\n");
		TRIGGER;
		goto failed;
	}

	txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
	// }}}

	txstr("ACMD6:   SET_BUS_WIDTH\r\n");
	// {{{
	_sdio->sd_data = 2;
	_sdio->sd_cmd  = 0x8140+6;
	wait_while_busy();
	if ((_sdio->sd_cmd & 0x81ff) != 0x0106) {
		txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
			txstr("\r\n");
		TRIGGER;
		goto failed;
	}

	txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
	txstr("  Data:    "); txhex(_sdio->sd_data); txstr("\r\n");
	// }}}

	_sdio->sd_phy = 0x09003c03;	// 25MHz, push-pull, 4b data width
	// _sdio->sd_phy = 0x0900bc03;	// .. and shut the unused clock down
	while(0x03 != (_sdio->sd_phy & 0x0ff))
		;

SETSCOPE;
	for(int sector=0; sector < 10; sector++) {
		txstr("CMD17:   READ_BLOCK "); txdecimal(sector); txstr("\r\n");
		// {{{
		for(int i=0; i<512/4; i++)
			_sdio->sd_fifa = 0x01020 + (sector * 4) + (i&3);
		_sdio->sd_data = (sector == 0) ? 0 : (sector + 0x02000-1);
		_sdio->sd_cmd  = 0x8940+17;
		TRIGGER;
		wait_while_busy();
		if ((_sdio->sd_cmd & 0x0c9ff) != 0x0111) {
			TRIGGER;
			txstr("ERROR: SD-CMD = "); txhex(_sdio->sd_cmd);
				txstr("\r\n");
			// goto failed;
		}

		txstr("  Cmd:     "); txhex(_sdio->sd_cmd); txstr("\r\n");
		txstr("  Data:    "); txhex(_sdio->sd_data); txstr(", sector:\r\n  ");

		for(int i=0; i<512/4; i++) {
			unsigned v;

			v = _sdio->sd_fifa;
			txstr("0x"); txhex(v);

			if (3 == (i & 3))
				txstr("\r\n  ");
			else
				txstr(" ");
		} txstr("\r\n");
	}
	// }}}

	txstr("Halting\r\n");
	zip_halt();
failed:
	txstr("EXIT on failure(s)\n");
#endif
}
