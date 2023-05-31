////////////////////////////////////////////////////////////////////////////////
//
// Filename:	videomode.h
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

