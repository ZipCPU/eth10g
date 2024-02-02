////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zipcpu/board/rxhdmi.c
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

	// Let the PI know there's nothing there ... yet
	(*_gpio) = GPIO_HDMIRXD_CLR;

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

	// Read the downstream EDID
	// {{{
	// Copy EDID to our I2C slave
	_i2c->ic_address = (unsigned)i2casm;

	// Wait for the EDID command to complete
	while(0 == (_i2c->ic_control & 0x0780000))
		;
	// }}}

	// Copy the EDID to stdout
	// {{{
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
	// }}}

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

	// Let the PI know we're up.  We need this to get the HDMIRX clock
	(*_gpio) = GPIO_HDMIRXD_SET;

	// Let's now let the clock lock, and release from reset
	// {{{
	// _hdmi->v_control = 0x04170;	// Release it all from reset
	_hdmi->v_control = // VCTRL_PIX_RESET |	// Release it all from reset
				VCTRL_PXCLK_HDMIIN
				| VCTRL_EXTERNAL_SRC
				| VCTRL_CMAP_2BGRY
				| VCTRL_ALPHA_0;
	// }}}

	// Check for the release from reset
	// {{{
	if (_hdmi->v_control & 1) {
		printf("Waiting for the pixel clock to lock ...\n");
		while(_hdmi->v_control & 1)
			;
	} printf("Pixel clock is locked, HDMIRX is released from reset\n");
	// }}}

	// Lock to the timing
	// {{{
	{
		unsigned	lock[32];
		unsigned	vsyncword;
		unsigned	sync = 0;

		for(int i=0; i<32; i++) {
			lock[i] = 0;

			_hdmi->v_fps = (i << 24) | (i<<16) | (i<<8);

			// Wait to get some statistics
			_zip->z_tma = 60000000;	// 600ms
			while(_zip->z_tma != 0)
				;

			vsyncword = _hdmi->v_syncword;
			lock[i] = vsyncword;
			printf("0x%02x - %08x\n", i, vsyncword);
		}

		for(int clr=0; clr<3; clr++) {
			int start = -1, dly=-1;
			for(int i=0; i<32; i++) {
				unsigned v = lock[i] >> (8*clr);

				if ((v & 0x10)&&(dly < 0 || dly == (v&0x0f))) {
					if (start < 0) {
						// printf("CLR#%d starts at %d\n", clr, i);
						start = i;
					} dly = (v & 0x0f);
				} else if (start >= 0) {
					// printf("CLR#%d ends at %d\n", clr, i);
					if (i-start > 10) {
						unsigned sv;
						sync &= ~(0x0ff << (8+(8*clr)));
						sv = start + (i-start)/2;
						sync |= (sv << (8+(8*clr)));

						// printf("CLR#%d set to %d\n", clr, sv);
					} start = -1; dly = -1;
				}
			}
		}

		printf("Setting sync word to: %08x\n", sync);
		_hdmi->v_fps = sync;
	}
	// }}}

	// Waiting for some video frames
	// {{{
	printf("Waiting for some frames to determine video format\n");
	_zip->z_tma = 0x7fffffff;
	while(_zip->z_tma != 0)
		;
	// }}}

	// Display the video output format
	// {{{
	printf("IN WIDTH   : %4d   IN HEIGHT  : %4d\n",
		_hdmi->v_in.m_width,  _hdmi->v_in.m_height);
	printf("IN H-PORCH : %4d   IN V-PORCH : %4d\n",
		_hdmi->v_in.m_hporch, _hdmi->v_in.m_vporch);
	printf("IN H-SYNC  :%s%4d   IN V-SYNC  :%s%4d\n",
		(_hdmi->v_in.m_hsync & 0x8000) ? "-":"+",
		_hdmi->v_in.m_hsync & 0x7fff,
		(_hdmi->v_in.m_hsync & 0x8000) ? "-":"+",
		 _hdmi->v_in.m_vsync & 0x7fff);
	printf("IN H-RAW   : %4d   IN V-RAW   : %4d\n",
		_hdmi->v_in.m_raw_width, _hdmi->v_in.m_raw_height);

	printf("SRC WIDTH  : %4d   SRC HEIGHT : %4d\n",
		_hdmi->v_src.m_width, _hdmi->v_src.m_height);
	printf("SRC H-PORCH: %4d   SRC V-PORCH: %4d\n",
		_hdmi->v_src.m_hporch, _hdmi->v_src.m_vporch);
	printf("SRC H-SYNC :%s%4d   SRC V-SYNC :%s%4d\n",
		(_hdmi->v_src.m_hsync & 0x8000) ? "-":"+",
		_hdmi->v_src.m_hsync & 0x07fff,
		(_hdmi->v_src.m_vsync & 0x8000) ? "-":"+",
		_hdmi->v_src.m_vsync & 0x07fff);
	printf("SRC H-RAW  : %4d   SRC V-RAW  : %4d\n",
		_hdmi->v_src.m_raw_width, _hdmi->v_src.m_raw_height);
	// }}}

	frq = _hdmi->v_sifreq;   printf("Si Clk   : %08x %10.6f MHz\n", frq, (double)frq / 1e6);
	frq = _hdmi->v_pxfreq;   printf("Pixel Clk: %08x %10.6f MHz\n", frq, (double)frq / 1e6);
	frq = _hdmi->v_hdmifreq; printf("Hdmi Clk : %08x %10.6f MHz\n", frq, (double)frq / 1e6);

	printf("HDMI setup complete\n");
#endif
}
