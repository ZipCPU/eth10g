////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	qkhdmi.c
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

	if ((*_gpio) & GPIO_HDMITXD)
		printf("HDMI TXD is *SET*\n");
	else
		printf("HDMI TXD is *CLEAR*\n");

	_hdmi->v_control = 1;	// Hold everything in reset for a while

	// Set up the empty image video mode
	// {{{
	_hdmi->v_src.m_width     = 800; _hdmi->v_src.m_height = 600;
	_hdmi->v_src.m_hporch    = 840; _hdmi->v_src.m_vporch = 601;
	_hdmi->v_src.m_hsync     = 968; _hdmi->v_src.m_vsync  = 605;
	_hdmi->v_src.m_raw_width =1056; _hdmi->v_src.m_raw_height = 628;
	// }}}

	// Set up the overlay
	// {{{
	_hdmi->v_overlay = grayimg;
	// We have a width of 800 pixels * 2 bits per pixel=>1600 bits=>200Bytes
	//	We have a bus width of 512 bits, or 64 bytes
	//	Lines must be bus aligned, we round 200Bytes up to the nearest
	//	  64 byte boundary, so ... ovmemwords = 256
	_hdmi->v_ovmemwords = 256; // (800*2+511)/512;
	_hdmi->v_ovheight= 491;
	_hdmi->v_ovhpos  =   0;
	_hdmi->v_ovypos  =  54;
	// }}}

	_hdmi->v_control = 0x0100;	// Release it all from reset

	_zip->z_tma = 0x7fffffff;
	while(_zip->z_tma != 0)
		;

	if ((*_gpio) & GPIO_HDMITXD)
		printf("HDMI TXD is *SET*\n");
	else
		printf("HDMI TXD is *CLEAR*\n");

	printf("SRC WIDTH  : %4d   SRC HEIGHT :%4d\n",
		_hdmi->v_src.m_width, _hdmi->v_src.m_height);
	printf("SRC H-PORCH:%4d    SRC V-PORCH:%4d\n",
		_hdmi->v_src.m_hporch, _hdmi->v_src.m_vporch);
	printf("SRC H-SYNC : %4d   SRC V-SYNC :%4d\n",
		_hdmi->v_src.m_hsync, _hdmi->v_src.m_vsync);
	printf("SRC H-RAW  : %4d   SRC V-RAW  :%4d\n",
		_hdmi->v_src.m_raw_width, _hdmi->v_src.m_raw_height);

	frq = _hdmi->v_sifreq;   printf("Si Clk   : %08x %9d\n", frq, frq);
	frq = _hdmi->v_pxfreq;   printf("Pixel Clk: %08x %9d\n", frq, frq);
	frq = _hdmi->v_hdmifreq; printf("Hdmi Clk : %08x %9d\n", frq, frq);

	printf("HDMI setup complete\n");
#endif
}
