////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rxhdmi.c
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generate an HDMI output image.
//
//	This is meant to test that we can receive an HDMI image, and transmit
//	the same with a second image overlayed partially on top of it.
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

#include "edid.c"

static	const	unsigned	VCTRL_PIX_RESET   = 0x00001,
				VCTRL_PXCLK_LOCAL = 0x00000,
				VCTRL_PXCLK_SICLK = 0x00010,
				VCTRL_PXCLK_HDMIIN= 0x00020,
				VCTRL_PXCLK_MASK  = 0x00030,
				VCTRL_EXTERNAL_SRC= 0x00040,
				VCTRL_SRC_MASK    = 0x00040,
				VCTRL_CMAP_BW     = 0x00000,
				VCTRL_CMAP_2BGRY  = 0x00100,
				VCTRL_CMAP_4BGRY  = 0x00200,
				VCTRL_CMAP_4BCMAP = 0x00300,
				VCTRL_CMAP_8BCMAP = 0x00400,
				VCTRL_CMAP_8B     = 0x00500,
				VCTRL_CMAP_16B    = 0x00600,
				VCTRL_CMAP_24B    = 0x00700,
				VCTRL_CMAP_MASK   = 0x00700,
				VCTRL_ALPHA_OPAQUE= 0x00000,
				VCTRL_ALPHA_0     = 0x04000,
				VCTRL_ALPHA_1     = 0x08000,
				VCTRL_TRANSPARENT = 0x0c000,
				VCTRL_ALPHA_MASK  = 0x0c000,
				VCTRL_LOCKED      = 0x10000,
				VCTRL_OVERLAY_ERR = 0x20000;

int main(int argc, char **argv) {
#ifndef	_BOARD_HAS_VIDPIPE
	printf("ERR: This design has no video pipe\n");
#else
	unsigned	frq, gp;

	if ((gp = *_gpio) & GPIO_HDMITXD)
		printf("HDMI TXD is *SET*\n");
	else {
		printf("HDMI TXD is *CLEAR*. (%08x)\n"
			"This means no monitor is present to receive our HDMI output.\n"
			"Now waiting for one to be plugged in ...\n", gp);
		while(0 == ((*_gpio) & GPIO_HDMITXD))
			;
	}

	_hdmi->v_control = VCTRL_PIX_RESET
				| VCTRL_PXCLK_HDMIIN
				| VCTRL_EXTERNAL_SRC
				| VCTRL_CMAP_2BGRY
				| VCTRL_ALPHA_0;

	// Copy EDID to our I2C slave
	_i2c->ic_address = (unsigned)i2casm;

	// Wait for the EDID command to complete
	while(0 == (_i2c->ic_control & 0x0780000))
		;

	// Copy the EDID to stdout
	for(int k=0; k<256; k++) {
		char	edidb;

		edidb = _edid[k];
		printf("%02x", edidb);
		if (15 == (k&15))
			printf("\n");
		else if (7 == (k&15))
			printf("   ");
		else
			printf(" ");
	}

	// Wait for the EDID to be read by the Pi
		// We have no signal for this ...

	// Look for the RX clock and imagery

	// Set up the overlay
	// {{{
	_hdmi->v_overlay = 0;	// Keep it turned off
/*
	_hdmi->v_overlay = grayimg;
	// We have a width of 800 pixels * 2 bits per pixel=>1600 bits=>200Bytes
	//	We have a bus width of 512 bits, or 64 bytes
	//	Lines must be bus aligned, we round 200Bytes up to the nearest
	//	  64 byte boundary, so ... ovmemwords = 256
	_hdmi->v_ovmemwords = 256; // (800*2+511)/512;
	_hdmi->v_ovheight= 491;

	// This position will be wrong for a larger screen, but should be enough
	// to demo the capability
	_hdmi->v_ovhpos  =   0;
	_hdmi->v_ovypos  =  54;
*/
	// }}}

	// Let the PI know we're up
	(*_gpio) = GPIO_HDMIRXD_SET;

	_hdmi->v_control = 0x04170;	// Release it all from reset
	_hdmi->v_control = // VCTRL_PIX_RESET |	// Release it all from reset
				VCTRL_PXCLK_HDMIIN
				| VCTRL_EXTERNAL_SRC
				| VCTRL_CMAP_2BGRY
				| VCTRL_ALPHA_0;

	_zip->z_tma = 0x7fffffff;
	while(_zip->z_tma != 0)
		;

	printf("IN WIDTH   : %4d   IN HEIGHT  :%4d\n",
		_hdmi->v_in.m_width,  _hdmi->v_in.m_height);
	printf("IN H-PORCH :%4d    IN V-PORCH :%4d\n",
		_hdmi->v_in.m_hporch, _hdmi->v_in.m_vporch);
	printf("IN H-SYNC  : %4d   IN V-SYNC  :%4d\n",
		_hdmi->v_in.m_hsync,  _hdmi->v_in.m_vsync);
	printf("IN H-RAW   : %4d   IN V-RAW   :%4d\n",
		_hdmi->v_in.m_raw_width, _hdmi->v_in.m_raw_height);

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
