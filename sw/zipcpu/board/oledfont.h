////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/oledfont.h
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
#ifndef	OLEDFONT_H
#define	OLEDFONT_H
// }}}

typedef struct	OLEDFONT_S {
	int	m_height, m_fixed;
	int	m_ln[256];
	const char	*m_datp[256];
} OLEDFONT;

extern	void	init_tall_glyfs(void);
extern	void	init_short_glyfs(void);
extern	void	set_fixed(OLEDFONT *f);

extern	OLEDFONT	*tallfontp;
extern	OLEDFONT	*shortfontp;

#endif
