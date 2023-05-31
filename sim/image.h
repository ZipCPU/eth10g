////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	image.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A generic image manipulation class with a few features.
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
#ifndef	IMAGE_H
#define	IMAGE_H

template<class PIXEL> class IMAGE {
protected:
	unsigned char	*m_buf;
	void	allocbuf(int h, int w);
	void	deallocb(void);
public:
	int	m_height, m_width;
	PIXEL	**m_img;
	PIXEL	*m_data;

	IMAGE(int h, int w);
	IMAGE(IMAGE *imgp);
	~IMAGE() { delete[] m_buf; }
	long	size(void) const { return m_height*m_width; }
	IMAGE *crop(int x, int y, int h, int w);

	void	zeroize(void);
	IMAGE	*copy(void);
	void	flipy(void);
	void	flipx(void);

	int	height(void) const { return m_height; }
	int	cols(void) const { return m_height; }
	int	width(void) const { return m_width; }
	int	rows(void) const { return m_width; }
};

typedef	IMAGE<unsigned char>	UCIMAGE, *PIMAGE;
typedef	IMAGE<int>		IIMAGE, *PIIMAGE;
typedef	IMAGE<double>		DIMAGE, *PDIMAGE;
#ifdef	COMPLEX_H
typedef	IMAGE<COMPLEX>		CIMAGE, *PCIMAGE;
#endif

#endif
