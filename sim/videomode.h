////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/videomode.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	In order to facilitate being able to handle multiple different
//		video mode simulations, this class encapsulates both the
//	video mode that the user is attempting to produce, as well as the
//	various front/back porch settings associated with that mode.
//
//	Modes are set upon creation, and not changed afterwards.  Modes may
//	be set via a display size, as well as via a pair of mode line
//	strings--one for each of horizontal and vertical.
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
//
// }}}
#ifndef	VIDEOMODE_H
#define	VIDEOMODE_H

class	VIDEOMODE {
protected:
	typedef struct	SMODE_S {
		int	m_data, m_front, m_synch, m_total;
	} SMODE;

	SMODE	m_h, m_v;
	bool	m_err;

	void	zeromode(SMODE &m) {
		m.m_front = m.m_synch = m.m_data = m.m_total = 0;
	}

	void	setline(SMODE &m, const char *ln) {
		const	char	DELIMITERS[] = ", \t\n";
		char	*tbuf, *ptr;

		tbuf = strdup(ln);

		ptr = strtok(tbuf, DELIMITERS);
		if (!ptr) {
			m_err = true;
			free(tbuf);
			return;
		}
		m.m_data = atoi(ptr);

		ptr = strtok(NULL, DELIMITERS);
		if (!ptr) {
			m_err = true;
			free(tbuf);
			return;
		}
		m.m_front = atoi(ptr);

		ptr = strtok(NULL, DELIMITERS);
		if (!ptr) {
			m_err = true;
			free(tbuf);
			return;
		}
		m.m_synch = atoi(ptr);

		ptr = strtok(NULL, DELIMITERS);
		if (!ptr) {
			m_err = true;
			free(tbuf);
			return;
		}
		m.m_total = atoi(ptr);

		if (m.m_data >= m.m_front)
			m_err = true;
		else if (m.m_front >= m.m_synch)
			m_err = true;
		else if (m.m_synch >= m.m_total)
			m_err = true;

		free(tbuf);
		return;
	}
public:
	
	VIDEOMODE(SMODE h, SMODE v) : m_h(h), m_v(v) {
		m_err = false;
	}

	VIDEOMODE(const char *h, const char *v) {

		m_err = false;
		setline(m_h, h);
		setline(m_v, v);

		if (m_err) {
			zeromode(m_h);
			zeromode(m_v);
		}
	}


//"800x600" 40.00     800 840 968 1056 600 601 605 628
//"1024x768" 65.00   1024 1048 1184 1344 768 771 777 806
//"1280x720" 74.25   1280 1720 1760 1980 720 725 730 750
//"1280x720" 74.18   1280 1390 1430 1650 720 725 730 750
//"1280x720" 74.25   1280 1390 1430 1650 720 725 730 750
//"1280x768" 68.25   1280 1328 1360 1440 768 771 778 790
//"1280x1024" 108.00 1280 1328 1440 1688 1024 1025 1028 1066
//"1360x768" 85.50   1360 1424 1536 1792 768 771 778 795 
//"720x480" 27.00    1440 1478 1602 1716 480 488 494 524
//"720x576" 27.00    1440 1464 1590 1728 576 580 586 624
	VIDEOMODE(const int h, const int v) {
		m_err = false;
		if ((h==640)&&(v==480)) {
			// 640 664 736 760 480 482 488 525
			setline(m_h, "640 656 752 800");
			setline(m_v, "480 490 492 521");
		} else if ((h==720)&&(v == 480)) {
			setline(m_h, "720 760 816 856");
			setline(m_v, "480 482 488 525");
		} else if ((h==768)&&(v == 483)) {
			setline(m_h, "768 808 864 912");
			setline(m_v, "483 485 491 525");
		} else if ((h == 800)&&(v == 600)) {
			setline(m_h, "800 840 968 1056");
			setline(m_v, "600 601 605 628");
		} else if ((h == 1024)&&(v == 768 )) {
			setline(m_h, "1024 1048 1184 1344");
			setline(m_v, "768 771 777 806");
		} else if ((h==1280)&&(v == 720)) {
			setline(m_h, "1280 1320 1376 1648");
			setline(m_v, "720 722 728 750");
		} else if ((h==1280)&&(v == 1024)) {
			setline(m_h, "1280 1328 1440 1688");
			setline(m_v, "1024 1025 1028 1066");
		} else if ((h==1920)&&(v == 1080)) {
			setline(m_h, "1920 1960 2016 2200");
			setline(m_v, "1080 1082 1088 1125");
		} else m_err = true;
	}

	int	height(void) const {
		return m_v.m_data;
	}

	int	width(void) const {
		return m_h.m_data;
	}

	//
	int	raw_height(void) const {
		return m_v.m_total;
	}

	int	raw_width(void) const {
		return m_h.m_total;
	}

	int	sync_pixels(void) const {
		return m_h.m_synch - m_h.m_front;
	}

	int	sync_lines(void) const {
		return m_v.m_synch - m_v.m_front;
	}

	int	hsync(void) const {
		return m_h.m_synch;
	}
	int	vsync(void) const {
		return m_v.m_synch;
	}

	int	pixels_per_frame(void) const {
		return m_v.m_total * m_h.m_total;
	}

	int	vback_porch(void) const {
		return m_v.m_total - m_v.m_synch;
	}

	int	hback_porch(void) const {
		return m_h.m_total - m_h.m_synch;
	}

	int	hporch(void) const {
		return m_h.m_front;
	}
	int	vporch(void) const {
		return m_v.m_front;
	}

	int	err(void) const {
		return m_err;
	}
};

#endif // VIDEOMODE_H

