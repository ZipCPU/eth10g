////////////////////////////////////////////////////////////////////////////////
//
// Filename:	hdmisim.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is the main simulator source code file.  It uses gtkmm
//		to create both an off-screen drawing area, as well as a
//	DrawingArea to display the "image" sent from the Verilog code to the
//	slave/output "monitor".
//
//	There is also a window class that holds this VGA simulation, called
//	HDMIWIN.  This is a top level window with just the one child, the
//	simulation window.
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
#include <stdio.h>
#include <stdlib.h>

#include <gtkmm.h>

#include "hdmisim.h"
#include "image.cpp"

const int VIDEO_GUARD = 0,
	VIDEO_DATA  = 1,
	CTL_PERIOD  = 2,
	DATA_GUARD  = 3,
	DATA_ISLAND = 4,
	HDMI_LOST   = 5;

int	gbl_nframes = 0;
const	int	HDMISIM::CLOCKS_PER_PIXEL = 1,
		HDMISIM::BITS_PER_COLOR=8;
const	bool	HDMISIM::m_debug = false;

void	HDMISIM::on_realize() {
	Gtk::DrawingArea::on_realize();

	m_pix = Cairo::ImageSurface::create(Cairo::FORMAT_RGB24,
		m_mode.width(), m_mode.height());
	m_gc  = Cairo::Context::create(m_pix);

	m_gc->set_source_rgb(0.0,0.0,0.0);
	m_gc->rectangle(0, 0, m_mode.width(), m_mode.height());
	m_gc->fill();

	m_state = CTL_PERIOD;
	m_state_counter = 0;
};

void	HDMISIM::get_preferred_width_vfunc(int &min, int &nw) const {
	min = m_mode.width(); nw = m_mode.width();
} void	HDMISIM::get_preferred_width_for_height_vfunc(int h,
		int &min, int &nw) const {
	min = m_mode.width(); nw = m_mode.width();
}

void	HDMISIM::get_preferred_height_vfunc(int &min, int &nw) const {
	min = m_mode.height(); nw = m_mode.height();
}
void	HDMISIM::get_preferred_height_for_width_vfunc(int w,
		int &min, int &nw) const {
	min = m_mode.height(); nw = m_mode.height();
}

#define	VIDEO_GUARD	0
#define	VIDEO_DATA	1
#define	CTL_PERIOD	2
#define	DATA_GUARD	3
#define	DATA_ISLAND	4

int	HDMISIM::bitreverse(int val) {
	// {{{
	int	result = 0, tmp = val;

	for(int k=0; k<10; k++) {
		result <<= 1;
		result |= (tmp&1);
		tmp >>= 1;
	}

	return result;
}
// }}}

bool	HDMISIM::isguard(int val) {
	// {{{
	if ((val == 0x2cc)||(val == 0x133))
		return true;
	return false;
}
// }}}

int	HDMISIM::ctldata(int val) {
	// {{{
	switch(val) {
	case 0x354:	return 0;
	case 0x0ab:	return 1;
	case 0x154:	return 2;
	case 0x2ab:	return 3;
	default:	return -1;
	}
}
// }}}

int	HDMISIM::pktdata(int val) {
	// {{{
	switch(val) {
	case 0x29c:	return 0;
	case 0x263:	return 1;
	case 0x2e4:	return 2;
	case 0x2e2:	return 3;
	//
	case 0x171:	return 4;
	case 0x11e:	return 5;
	case 0x18e:	return 6;
	case 0x13c:	return 7;
	//
	case 0x2cc:	return 8;
	case 0x139:	return 9;
	case 0x19c:	return 10;
	case 0x2c6:	return 11;
	//
	case 0x28e:	return 12;
	case 0x271:	return 13;
	case 0x163:	return 14;
	case 0x2c3:	return 15;
	default:	return -1;
	}
}
// }}}

int	HDMISIM::pixeldata(int val) {
	// {{{
	int	midp, result = 0;

	midp = val & 0x3ff;
	if (midp&1)
		midp ^= 0x3fc;

	midp ^= (midp >> 1);
	if ((val&2)==0)
		midp ^= 0x01fc;

	midp &= 0x03fc;

	result = bitreverse(midp);
	return result;
}
// }}}

void	HDMISIM::operator()(const int blu, const int grn, const int red) {
	// {{{
	int	brblu, brgrn, brred, r=0, g=0, b=0, hsync, vsync, s;
	int	xv, yv;

	brblu = bitreverse(blu);
	brgrn = bitreverse(grn);
	brred = bitreverse(red);
	hsync = vsync = 0;

	bool	video_guard, data_guard;
	// bool	video_preamble, data_preamble;

	video_guard = ((isguard(brblu))&&(isguard(brgrn))&&(isguard(brred)));
	if (brblu != brred)
		video_guard = false;
	else if (brblu == brgrn)
		video_guard = false;

	/*
	video_preamble = ((ctldata(brblu)==0)
				&&(ctldata(brgrn)==1)
				&&(ctldata(brred)==0));

	data_preamble = ((ctldata(brgrn)==1)
				&&(ctldata(brred)==1));
	*/

	data_guard = (((ctldata(brblu)&~3)==0x0c)
			&&(isguard(brgrn))&&(isguard(brred)));

	//
	// Set some default decode values
	//
	s = ctldata(brblu);
	if ((s&~0x0f) == 0) {
		hsync = s & 1;
		vsync = (s & 2) ? 1:0;
	}
	b = pixeldata(blu);
	g = pixeldata(grn);
	r = pixeldata(red);

	if (video_guard) {
		if (m_state != VIDEO_GUARD) {
			m_state = VIDEO_GUARD;
			if (m_debug) printf("State -> VIDEO_GUARD, %d\n", m_state_counter);
			m_state_counter = 0;
		} else
			m_state_counter++;
		hsync = 0;
		vsync = 0;
	} else if (m_state == VIDEO_DATA) {
		hsync = 0;
		vsync = 0;
		m_state_counter ++;
	} else if (m_state == CTL_PERIOD) {
		if (s < 0) {
			m_state = HDMI_LOST;
			m_out_of_sync = true;
		} else if (data_guard) {
			if (m_debug) printf("State -> DATA_GUARD, %d\n", m_state_counter);
			m_state = DATA_GUARD;
			m_state_counter = 0;
		} else // if ((data_preamble)||(video_preamble))
			m_state_counter++;
	} else if (m_state == DATA_GUARD) {
		if (!data_guard) {
			if (m_debug) printf("State -> DATA_ISLAND, %d\n", m_state_counter);
			m_state = DATA_ISLAND;
			m_state_counter = 0;
		} else
			m_state_counter++;
	} else if (m_state == DATA_ISLAND) {
		if (m_state_counter >= 64) {
			if (data_guard) {
				if (m_debug) printf("State -> DATA_GUARD, %d\n", m_state_counter);
				m_state = DATA_GUARD;
				m_state_counter = 0;
			} else {
				if (m_debug) printf("State -> OUT-OF-SYNC, %d\n", m_state_counter);
				m_out_of_sync = true;
				m_state_counter = 0;
			}
		} else
			m_state_counter++;
	} else if (m_state == VIDEO_GUARD) {
		// if (!video_guard)	// Always true
		if (m_debug) printf("State -> VIDEO_DATA, %d\n", m_state_counter);
		m_state = VIDEO_DATA;
		m_state_counter = 0;
		hsync = 0;
		vsync = 0;

		int	new_hsync = m_mode.sync_pixels()+m_mode.hback_porch()-1;
		//if (!m_out_of_sync)
			//; // assert(new_hsync == m_hsync_count);
		//else
			m_hsync_count = new_hsync;
	} else { // if (m_state == HDMI_LOST)
		m_out_of_sync = true;
	}

	if (0 && (m_debug)&&(m_out_of_sync))
		printf("S(#%d/%4d):HDMISIM--TICK(%d,%d,%6d,%6d)\n", m_state,
				m_state_counter,
				vsync, hsync, m_vsync_count, m_hsync_count);

	if (++m_pixel_clock_count < CLOCKS_PER_PIXEL) {
		bool	not_same = false;
		if (vsync != m_last_vsync)
			not_same = true;
		else if (hsync != m_last_hsync)
			not_same = true;
		else if (r != m_last_r)
			not_same = true;
		else if (g != m_last_g)
			not_same = true;
		else if (b != m_last_b)
			not_same = true;
		if (not_same) {
			if (!m_out_of_sync)
				printf("%30s\n", "PX-RESYNC");
			m_pixel_clock_count = 0;
			m_out_of_sync = true;
		}
	} else {
		m_pixel_clock_count = 0;

		if ((vsync)&&(!m_last_vsync)) {
			//
			// On the first time vsync is dropped, we'll declare
			// this to be the beginning of the synchronization
			// period
			//
			if ((m_vsync_count != 0)
				&&(m_vsync_count != m_mode.raw_width() * m_mode.raw_height()-1)) {
				// Lose synch
				m_out_of_sync = true;
				printf("%30s (%d, %d)\n", "V-RESYNC",
					m_vsync_count,
					m_mode.raw_width() * m_mode.sync_lines()-1);
			} else if (m_debug)
				printf("\nHDMI-FRAME\n");

			gbl_nframes++;

			m_vsync_count = 0;
			m_out_of_sync = false;
			if ((m_hsync_count != m_mode.raw_width())&&(!m_out_of_sync)) {
				m_vsync_count = 0;
				// printf("H-RESYNC(V)\n");
				// m_out_of_sync = true;
			}

		} else if (vsync) {
			//
			// Count the number of clocks with vsync false
			//
			// These would be during the vertical sync pulse,
			// since it is active low.  There should be
			// m_mode.sync_lines() lines of this pulse being high.
			//
			if (m_vsync_count < m_mode.sync_lines()*m_mode.raw_width() - 1)
				m_vsync_count++;
			else {
				// If we've got too many of them, then
				// declare us to be out of synch.
				if (!m_out_of_sync) {
					m_out_of_sync = true;
					printf("%30s (%d, %d)\n", "V-RESYNC (TOO MANY)",
					m_vsync_count,
					m_mode.raw_width() * m_mode.sync_lines()-1);
				}
				m_vsync_count = m_mode.sync_lines()*m_mode.raw_width() - 1;
			}
		} else
			m_vsync_count++;

		if ((hsync)&&(!m_last_hsync)) {
			// On the first hsync pulse, we start counting pixels.
			// There should be exactly raw_width() pixels per line.
			if ((m_hsync_count != m_mode.raw_width()-1)&&(!m_out_of_sync)) {
				printf("H-RESYNC\n");
				printf("\n%30s (%d,%d)\n","H-RESYNC (Wrong #)", m_hsync_count, m_mode.raw_width());
				m_hsync_count = 0;
				m_out_of_sync = true;
			}

			m_hsync_count = 0;
		} else if (hsync) {
			// During the horizontal sync, we expect
			// m_mode.sync_pixels() pixels with the hsync low.
			if (m_hsync_count < m_mode.sync_pixels() - 1)
				m_hsync_count++;
			else {
				// Too many pixels with m_mode.sync_pixels()
				// low, and we are out of synch.
				m_hsync_count = m_mode.sync_pixels() - 1;
				if (!m_out_of_sync) {
					m_vsync_count = 0;
					printf("\n%30s (%d,%d)\n","H-RESYNC (TOO-MANY)", m_hsync_count, m_mode.raw_width());
					m_out_of_sync = true;
				}
			}
		} else
			// Otherwise .... just count horizontal pixels
			// from the first synch pixel
			m_hsync_count++;

		// HSYNC_COUNT
		// Starts at 0 on the first sync pulse clock period,
		//	and increments from there
		// 0... (sync_pixels()-1)	Sync is true
		// (sync_pixels)...(hback_porch-1)	Sync is false, no data
		// (hback_porch ... hback_porch+width-1)
		// (raw_width-front_porch ... raw_width)
		bool	error = false;

		if (m_vsync_count >= m_mode.raw_height()*m_mode.raw_width())
			error = true;
		if (hsync && (m_hsync_count >= m_mode.sync_pixels()))
			error = true;
		if ( m_hsync_count >= m_mode.raw_width())
			error = true;

		if (error) {
			if ( m_hsync_count >=  m_mode.raw_width())
				printf("3 - ");
			printf("OUT-OF-BOUNDS sync count: %d, %d [%d, %d, %dx%d=%d]\n",
				m_hsync_count, m_vsync_count,
				m_mode.raw_width(),
				m_mode.sync_pixels(),
				m_mode.raw_height(),
				m_mode.raw_width(),
				m_mode.raw_height() * m_mode.raw_width());
			m_pixel_clock_count = 0;
			m_out_of_sync = true;
			m_hsync_count = 0;
			m_vsync_count = 0;


			printf("\t%d x %d (within %d x %d)\n",
				m_mode.width(), m_mode.height(),
				m_mode.raw_width(), m_mode.raw_height());
		}

		yv = (m_vsync_count-m_hsync_count)/m_mode.raw_width();
		yv -= m_mode.vback_porch() + m_mode.sync_lines();
		xv = (m_hsync_count) -(m_mode.sync_pixels() + m_mode.hback_porch());

		if (!error && (xv >= 0)&&(yv >= 0) // only if in range
				&&(xv < m_mode.width())&&(yv < m_mode.height())
				&&(!m_out_of_sync)) {
			int	clr, msk = (1<<BITS_PER_COLOR)-1;
			clr = ((r&msk)<<(24-BITS_PER_COLOR))
					|((g&msk)<<(16-BITS_PER_COLOR))
					|((b & msk)<<(8-BITS_PER_COLOR));
			if (m_data->m_img[yv][xv] != (unsigned)clr) {
				m_data->m_img[yv][xv] = clr;

				// printf("\nIMG[%03d][%03d] = %03x\n",
				//		yv, xv, clr);
				m_gc->set_source_rgb(
					(r&msk)/(double)(msk),
					(g&msk)/((double)msk),
					(b&msk)/((double)msk));
				m_gc->rectangle(xv, yv, 1, 1);
				m_gc->fill();

				queue_draw_area(xv, yv, 1, 1);
				// m_window->invalidate_rect(Gdk::Rectangle(
				// 	xv, yv, 1, 1), true);
			}

		}

		int	eol = m_mode.width() + m_mode.sync_pixels()
				// + m_mode.hporch();
				+ m_mode.hback_porch();
		if ((m_state == VIDEO_DATA)
				&&(m_hsync_count > eol)) {
			if (m_debug) printf("State -> CTL_PERIOD, %d\n", m_state_counter);
			m_state = CTL_PERIOD;
			m_state_counter = 0;
		}

		// else if (!m_out_of_sync)
		//	printf("IMG[%03d][%03d] (Out-of-bounds)\n", yv, xv);
	}

	m_last_vsync = vsync;
	m_last_hsync = hsync;
	m_last_r     = r;
	m_last_g     = g;
	m_last_b     = b;
}
// }}}

bool	HDMISIM::on_draw(CONTEXT &gc) {
	// {{{
	// printf("ON-DRAW\n");
	gc->save();
	gc->set_source(m_pix, 0, 0);
	gc->paint();
	gc->restore();

	return true;
}
// }}}

void	HDMIWIN::init(void) {
	// {{{
	m_hdmisim->set_size_request(SIMWIN::width(),SIMWIN::height());
	set_border_width(0);
	add(*m_hdmisim);
	show_all();
	Gtk::Window::set_title(Glib::ustring("HDMI Simulator"));
};
// }}}

HDMIWIN::HDMIWIN(void) : SIMWIN(640,480) {
	//  {{{
	m_hdmisim = new HDMISIM(640, 480);
	init();
}
// }}}

HDMIWIN::HDMIWIN(const int w, const int h) : SIMWIN(w,h) {
	m_hdmisim = new HDMISIM(w, h);
	init();
}

HDMIWIN::HDMIWIN(const char *h, const char *v) : SIMWIN(h, v) {
	m_hdmisim = new HDMISIM(h, v);
	init();
}

