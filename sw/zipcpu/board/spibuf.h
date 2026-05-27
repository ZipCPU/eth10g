////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/spibuf.h
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
// Copyright (C) 2025-2026, Gisselquist Technology, LLC
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
#ifndef	SPIBUF_H
#define	SPIBUF_H
// }}}

typedef	struct	SPIBUF_S {
	int	i_ln, i_bufsz, i_stopped, i_lastp;
	char	i_b[1];
} SPIBUF;

extern	SPIBUF *spib_new(int);
extern	void spib_clear(SPIBUF *);
extern	void spib_append(SPIBUF *, char);
extern	void spib_appendi(SPIBUF *, char);
extern	void spib_start(SPIBUF *, char);
extern	void spib_stop(SPIBUF *);

extern	void spib_read(SPIBUF *, int);
extern	void spib_send(SPIBUF *, int, char *);
extern	void spib_sendc(SPIBUF *, char);
extern	void spib_txrx(SPIBUF *, int, char *);
extern	void spib_txrxc(SPIBUF *, char);
extern	void spib_last(SPIBUF *);

extern	void spib_wait(SPIBUF *);
extern	void spib_halt(SPIBUF *);
extern	void spib_tick(SPIBUF *);
extern	void spib_target(SPIBUF *);
extern	void spib_jump(SPIBUF *);
extern	void spib_channel(SPIBUF *, int);
extern	void spib_noop(SPIBUF *);

#endif
