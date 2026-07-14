////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/oledfb.h
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
#ifndef	OLEDFB_H
#define	OLEDFB_H
// }}}

extern	OLEDFONT	*fb_font;
// struct	I2CCPU;

// The OLED "framebuffer"
typedef	struct	OLED_FB_S {
	I2CCPU	*dev;
	int	W, H, wrap, dirty;
	int	x, y;
	char	b[1];
} OLED_FB;

extern	void	oled_hwsetup(void);
extern	void	oled_init(void);
extern	void	oled_clear(void);
extern	void	oled_clear_eol(void);
extern	void	oled_scroll(int count);
extern	void	oled_move(int x, int y);
extern	void	oled_char(const char ch);
extern	void	oled_write(const char *str);
extern	void	oled_flush(void);
extern	int	oled_busy(void);
extern	void	oled_dump(void);

#endif
