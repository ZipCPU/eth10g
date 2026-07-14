////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/i2cbuf.h
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
#ifndef	I2CBUF_H
#define	I2CBUF_H
// }}}

typedef	struct	I2CBUF_S {
	int	i_ln, i_bufsz, i_half;
	char	i_b[1];
} I2CBUF;

extern	I2CBUF *i2cb_new(int);
extern	void i2cb_clear(I2CBUF *);
extern	void i2cb_append(I2CBUF *, char);
extern	void i2cb_noop(I2CBUF *);
extern	void i2cb_start(I2CBUF *);
extern	void i2cb_stop(I2CBUF *);

extern	void i2cb_addr(I2CBUF *, int);
extern	void i2cb_read(I2CBUF *, int);
extern	void i2cb_rdlast(I2CBUF *, int);
extern	void i2cb_send(I2CBUF *, int, char *);
extern	void i2cb_sendc(I2CBUF *, char);

extern	void i2cb_wait(I2CBUF *);
extern	void i2cb_halt(I2CBUF *);
extern	void i2cb_target(I2CBUF *);
extern	void i2cb_jump(I2CBUF *);
extern	void i2cb_channel(I2CBUF *, unsigned);

extern	void i2cb_dump(I2CBUF *);

#endif
