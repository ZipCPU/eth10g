////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/ssdlogo.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Instructions for the I2C CPU, to generate a logo output on the
//		SSD1306.
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
// }}}
//


const char i2casm[] = {
	0x13, 0xe8, 0x30, 0x07, 0x21, 0x30, 0x78, 0x30,
	0x80, 0x30, 0xae, 0x30, 0x80, 0x30, 0xd5, 0x30,
	0x80, 0x30, 0x80, 0x30, 0x80, 0x30, 0xa8, 0x30,
	0x80, 0x30, 0x1f, 0x30, 0x80, 0x30, 0xd3, 0x30,
	0x80, 0x30, 0x00, 0x30, 0x80, 0x30, 0x40, 0x30,
	0x80, 0x30, 0x8d, 0x30, 0x80, 0x30, 0x14, 0x30,
	0x80, 0x30, 0x20, 0x30, 0x80, 0x30, 0x01, 0x30,
	0x80, 0x30, 0xa0, 0x30, 0x80, 0x30, 0xc0, 0x30,
	0x80, 0x30, 0xda, 0x30, 0x80, 0x30, 0x02, 0x30,
	0x80, 0x30, 0x81, 0x30, 0x80, 0x30, 0x8f, 0x30,
	0x80, 0x30, 0xd9, 0x30, 0x80, 0x30, 0xf1, 0x30,
	0x80, 0x30, 0xdb, 0x30, 0x80, 0x30, 0x40, 0x30,
	0x80, 0x30, 0xa4, 0x30, 0x80, 0x30, 0xa6, 0x30,
	0x80, 0x30, 0x2e, 0x30, 0x80, 0x30, 0x20, 0x30,
	0x80, 0x30, 0x01, 0x30, 0x80, 0x30, 0x21, 0x30,
	0x80, 0x30, 0x00, 0x30, 0x80, 0x30, 0x7f, 0x30,
	0x80, 0x30, 0x22, 0x30, 0x80, 0x30, 0x00, 0x30,
	0x80, 0x30, 0x03, 0x13, 0x78, 0x30, 0x40, 0x30,
	0xc0, 0x30, 0x00, 0x30, 0x1c, 0x30, 0xf0, 0x30,
	0xc0, 0x30, 0x00, 0x30, 0x1c, 0x30, 0xe0, 0x30,
	0xff, 0x30, 0xfc, 0x30, 0xff, 0x30, 0xc7, 0x30,
	0xff, 0x30, 0xfc, 0x30, 0xff, 0x30, 0x8f, 0x30,
	0xff, 0x30, 0xfc, 0x30, 0xff, 0x30, 0x1f, 0x30,
	0xff, 0x30, 0xfc, 0x30, 0xff, 0x30, 0x3f, 0x30,
	0xff, 0x30, 0xfc, 0x30, 0xff, 0x30, 0x3f, 0x30,
	0xff, 0x30, 0xfc, 0x30, 0xff, 0x30, 0x3f, 0x30,
	0xff, 0x30, 0xfc, 0x30, 0xff, 0x30, 0x3f, 0x30,
	0xff, 0x30, 0x3c, 0x30, 0x80, 0x30, 0x3f, 0x30,
	0xff, 0x30, 0x3c, 0x30, 0x80, 0x30, 0x3f, 0x30,
	0xff, 0x30, 0x3c, 0x30, 0xff, 0x30, 0x3f, 0x30,
	0xff, 0x30, 0x3c, 0x30, 0xff, 0x30, 0x3f, 0x30,
	0xff, 0x30, 0x3c, 0x30, 0xfe, 0x30, 0x1f, 0x30,
	0xff, 0x30, 0x3c, 0x30, 0xfc, 0x30, 0x8f, 0x30,
	0xff, 0x30, 0x3c, 0x30, 0xf8, 0x30, 0xc7, 0x30,
	0xff, 0x30, 0x3c, 0x30, 0x01, 0x30, 0xe0, 0x30,
	0xff, 0x30, 0x3c, 0x30, 0x03, 0x30, 0xf0, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xe7, 0x30, 0xf7, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xc3, 0x30, 0xe7, 0x30, 0xff, 0x30,
	0xff, 0x30, 0x81, 0x30, 0xcf, 0x30, 0xff, 0x30,
	0xff, 0x30, 0x00, 0x30, 0x9f, 0x30, 0xff, 0x30,
	0xff, 0x30, 0x00, 0x30, 0x3f, 0x30, 0xff, 0x30,
	0xff, 0x30, 0x81, 0x30, 0x7f, 0x30, 0xfe, 0x30,
	0xff, 0x30, 0xc3, 0x30, 0xff, 0x30, 0xfc, 0x30,
	0xff, 0x30, 0xe7, 0x30, 0xff, 0x30, 0xf9, 0x30,
	0x8f, 0x30, 0xff, 0x30, 0xe1, 0x30, 0xf3, 0x30,
	0x07, 0x30, 0xff, 0x30, 0xc0, 0x30, 0xe7, 0x30,
	0x03, 0x30, 0x7e, 0x30, 0x80, 0x30, 0xcf, 0x30,
	0x01, 0x30, 0x3c, 0x30, 0x00, 0x30, 0x9f, 0x30,
	0x00, 0x30, 0x00, 0x30, 0x00, 0x30, 0x9f, 0x30,
	0x00, 0x30, 0x00, 0x30, 0x00, 0x30, 0x9f, 0x30,
	0x00, 0x30, 0x18, 0x30, 0x00, 0x30, 0x9f, 0x30,
	0x01, 0x30, 0x7c, 0x30, 0x80, 0x30, 0x9f, 0x30,
	0x03, 0x30, 0xfe, 0x30, 0xc0, 0x30, 0x8f, 0x30,
	0x07, 0x30, 0xff, 0x30, 0xe1, 0x30, 0xc7, 0x30,
	0x87, 0x30, 0xff, 0x30, 0xf3, 0x30, 0xe3, 0x30,
	0xc7, 0x30, 0xcf, 0x30, 0xff, 0x30, 0xe1, 0x30,
	0xe3, 0x30, 0x87, 0x30, 0xff, 0x30, 0xe0, 0x30,
	0xf1, 0x30, 0x03, 0x30, 0x7f, 0x30, 0xc0, 0x30,
	0xf9, 0x30, 0x01, 0x30, 0x3e, 0x30, 0x80, 0x30,
	0xf9, 0x30, 0x00, 0x30, 0x18, 0x30, 0x00, 0x30,
	0xf9, 0x30, 0x00, 0x30, 0x00, 0x30, 0x00, 0x30,
	0xf9, 0x30, 0x00, 0x30, 0x00, 0x30, 0x00, 0x30,
	0xf9, 0x30, 0x00, 0x30, 0x3c, 0x30, 0x80, 0x30,
	0xf3, 0x30, 0x01, 0x30, 0x7e, 0x30, 0xc0, 0x30,
	0xe7, 0x30, 0x03, 0x30, 0xff, 0x30, 0xe0, 0x30,
	0xcf, 0x30, 0x87, 0x30, 0xff, 0x30, 0xf1, 0x30,
	0x9f, 0x30, 0xff, 0x30, 0xe7, 0x30, 0xff, 0x30,
	0x3f, 0x30, 0xff, 0x30, 0xc3, 0x30, 0xff, 0x30,
	0x7f, 0x30, 0xfe, 0x30, 0x81, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xfc, 0x30, 0x00, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xf9, 0x30, 0x00, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xf3, 0x30, 0x81, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xe7, 0x30, 0xc3, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xef, 0x30, 0xe7, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0x03, 0x30, 0x00, 0x30, 0xf0, 0x30,
	0xff, 0x30, 0x00, 0x30, 0x00, 0x30, 0xf0, 0x30,
	0x7f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xe0, 0x30,
	0x3f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xe0, 0x30,
	0x1f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xe0, 0x30,
	0x0f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xc0, 0x30,
	0x0f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xc0, 0x30,
	0x07, 0x30, 0xf0, 0x30, 0xff, 0x30, 0xff, 0x30,
	0x07, 0x30, 0xf8, 0x30, 0xff, 0x30, 0xff, 0x30,
	0x07, 0x30, 0xfc, 0x30, 0xff, 0x30, 0xff, 0x30,
	0x07, 0x30, 0xfc, 0x30, 0xff, 0x30, 0xff, 0x30,
	0x07, 0x30, 0xfc, 0x30, 0xff, 0x30, 0xff, 0x30,
	0x07, 0x30, 0xfc, 0x30, 0xff, 0x30, 0xff, 0x30,
	0x07, 0x30, 0xf8, 0x30, 0xff, 0x30, 0xff, 0x30,
	0x07, 0x30, 0xf0, 0x30, 0xff, 0x30, 0xff, 0x30,
	0x0f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xfc, 0x30,
	0x0f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xf8, 0x30,
	0x1f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xf8, 0x30,
	0x3f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xf8, 0x30,
	0x7f, 0x30, 0x00, 0x30, 0x00, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0x00, 0x30, 0x00, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0x03, 0x30, 0x00, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0x07, 0x30, 0xf8, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x30,
	0xff, 0x30, 0xff, 0x30, 0xff, 0x30, 0xff, 0x13,
	0x78, 0x30, 0x80, 0x30, 0xa7, 0x30, 0x80, 0x30,
	0xaf, 0x29, 0x99
};
