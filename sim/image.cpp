////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/image.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A generic 2D image class
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
#include <stdlib.h>
#include <assert.h>
#include "image.h"

template<class PIXEL> void IMAGE<PIXEL>::allocbuf(int h, int w) {
	int	i, sz;

	sz = h*w*sizeof(PIXEL)+sizeof(PIXEL *)*h;
	m_buf = new unsigned char[sz];
	assert(m_buf);
				
	m_img  = (PIXEL **)m_buf;
	m_data = (PIXEL *)&m_buf[sizeof(PIXEL *)*h];
	for(i=0; i<h; i++)
		m_img[i] = &m_data[i*w];

	m_height = h;
	m_width  = w;
}


template<class PIXEL> IMAGE<PIXEL>::IMAGE(int h, int w) {
	allocbuf(h, w);
}

template<class PIXEL> IMAGE<PIXEL>::IMAGE(IMAGE<PIXEL> *img) {
	int	sz, i;

	allocbuf(img->m_height, img->m_width);
	sz = size();
	for(i=0; i<sz; i++)
		m_data[i] = img->m_data[i];
}

template<class PIXEL> IMAGE<PIXEL> *IMAGE<PIXEL>::crop(int y, int x,
			int h, int w) {
	IMAGE<PIXEL>	*r;
	int	xp, yp;

	assert((h>0)&&(w>0));
	assert(y+h <= m_height);
	assert(x+w <= m_width);

	r = new IMAGE<PIXEL>(h, w);

	for(yp=0; yp<h; yp++)
		for(xp=0; xp<w; xp++)
			r->m_img[yp][xp] = m_img[yp+y][xp+x];
	return r;
}

template<class PIXEL> void IMAGE<PIXEL>::zeroize(void) {
	int	ip, sz;

	sz = size();
	for(ip=0; ip<sz; ip++)
		m_data[ip] = 0;
}

template<class PIXEL> IMAGE<PIXEL> *IMAGE<PIXEL>::copy(void) {
	IMAGE<PIXEL>	*r;
	int	ip, sz;

	r = new IMAGE<PIXEL>(m_height, m_width);
	sz = size();
	for(ip=0; ip<sz; ip++)
		r->m_data[ip] = m_data[ip];
	return r;
}

template<class PIXEL> void IMAGE<PIXEL>::flipy(void) {
	int	r, c;
	PIXEL	tmp;

	// fprintf(stderr, "FLIPPING-Y (%d, %d)\n", height, width);
	for(r=0; r<m_height/2; r++) {
		for(c=0; c<m_width; c++) {
			  tmp                  = m_img[  r][c];
			m_img[           r][c] = m_img[m_height-1-r][c];
			m_img[m_height-1-r][c] = tmp;
		}
	}
}

template<class PIXEL> void IMAGE<PIXEL>::flipx(void) {
	int	r, c;
	PIXEL	tmp;

	// fprintf(stderr, "FLIPPING-X\n");
	for(r=0; r<m_height; r++) {
		for(c=0; c<m_width/2; c++) {
			  tmp                 = m_img[r][          c];
			m_img[r][          c] = m_img[r][m_width-1-c];
			m_img[r][m_width-1-c] = tmp;
		}
	}
}
