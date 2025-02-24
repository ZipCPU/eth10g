////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/qkhdmi.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generate an HDMI output image.
//
//	This is not meant to be a final product, but just the ability to
//	generate a quick image.  Our goal will be to use the 40MHz pixel
//	clock, to skip the HDMI RX, and just produce an image out.  Our
//	image will come from an external file (bwimag.c), and just get
//	copied to the screen via a frame buffer.
//
//	The image is designed to be read from a Flash based frame buffer.
//
//	This design depends upon the existence of the VideoPipe RTL component
//	within the RTL.  It will not function without it.
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

#include <stdio.h>
#include <zipsys.h>
#include "board.h"

#include "bwimag.c"

int main(int argc, char **argv) {
#ifndef	_BOARD_HAS_VIDPIPE
	printf("ERR: This design has no video pipe\n");
#else
	unsigned	frq;

	(*_gpio) = GPIO_TRACE_SET;

	if ((*_gpio) & GPIO_HDMITXD)
		printf("HDMI TXD is *SET*\n");
	else
		printf("HDMI TXD is *CLEAR*\n");

	_hdmi->v_control = 1;	// Hold everything in reset for a while

	// Set up the empty image video mode
	// {{{
	_hdmi->v_src.m_width     = 1360; _hdmi->v_src.m_height = 768;
	_hdmi->v_src.m_hporch    = 1424; _hdmi->v_src.m_vporch = 771;
	_hdmi->v_src.m_hsync     = 1536; _hdmi->v_src.m_vsync  = 778;
	_hdmi->v_src.m_raw_width = 1792; _hdmi->v_src.m_raw_height = 795;
	// }}}

	// Set up the overlay
	// {{{
	// Turn the overlay off so we can set it up
	_hdmi->v_overlay = (void *)0;
	// We have a width of 800 pixels * 2 bits per pixel=>1600 bits=>200Bytes
	//	We have a bus width of 512 bits, or 64 bytes
	//	Lines must be bus aligned, we round 200Bytes up to the nearest
	//	  64 byte boundary, so ... ovmemwords = 256
	//	That said, the Video pipe handler will handle all of that math
	//	for us, so we can just set this to 800 pixels and let the
	//	hardware handle the rest.
	_hdmi->v_ovmemwords = 800;
	_hdmi->v_ovheight= 491;	// Required, so we know when to stop reading
	_hdmi->v_ovhpos  = 280;	// Let's center our image: (1360-800)/2
	_hdmi->v_ovypos  = 138;	//	(768-491)/2
	_hdmi->v_overlay = grayimg;	// Pointer to the image itself
	// }}}

	_hdmi->v_control = 0x0100;	// Release it all from reset

	// _zip->z_tma = 0x7fffffff;
	// while(_zip->z_tma != 0)
	//	;

	if ((*_gpio) & GPIO_HDMITXD)
		printf("HDMI TXD is *SET*\n");
	else
		printf("HDMI TXD is *CLEAR*\n");

	printf("SRC WIDTH  : %4d   SRC HEIGHT : %4d\n",
		_hdmi->v_src.m_width, _hdmi->v_src.m_height);
	printf("SRC H-PORCH: %4d   SRC V-PORCH: %4d\n",
		_hdmi->v_src.m_hporch, _hdmi->v_src.m_vporch);
	printf("SRC H-SYNC : %4d   SRC V-SYNC : %4d\n",
		_hdmi->v_src.m_hsync, _hdmi->v_src.m_vsync);
	printf("SRC H-RAW  : %4d   SRC V-RAW  : %4d\n",
		_hdmi->v_src.m_raw_width, _hdmi->v_src.m_raw_height);

	frq = _hdmi->v_sifreq;   printf("Si Clk   : %08x %9d\n", frq, frq);
	frq = _hdmi->v_pxfreq;   printf("Pixel Clk: %08x %9d\n", frq, frq);
	frq = _hdmi->v_hdmifreq; printf("Hdmi Clk : %08x %9d\n", frq, frq);

	printf("HDMI setup complete\n");
#endif
}
