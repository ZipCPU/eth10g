////////////////////////////////////////////////////////////////////////////////
//
// Filename:	simwin.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	
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
#ifndef	SIMWIN_H
#define	SIMWIN_H

#include <gtkmm.h>
#include "image.h"
#include "videomode.h"

class	SIMWIN	: public Gtk::Window {
protected:
	VIDEOMODE	m_vmode;

public:
	SIMWIN(void) : m_vmode(640,480) {};
	SIMWIN(const int w, const int h) : m_vmode(w,h) {};
	SIMWIN(const char *h, const char *v) : m_vmode(h,v) {};

	virtual	bool syncd(void)  const= 0;

	int  width(void)  const {
		return m_vmode.width();
	}

	int  height(void) const {
		return	m_vmode.height();
	}

	int  raw_width(void)  const {
		return m_vmode.raw_width();
	}

	int  raw_height(void) const {
		return m_vmode.raw_height();
	}
	int  hsync(void)  const {
		return	m_vmode.hsync();
	}
	int  vsync(void)  const {
		return	m_vmode.vsync();
	}
	int hporch(void)  const {
		return	m_vmode.hporch();
	}
	int vporch(void)  const {
		return	m_vmode.vporch();
	}
	int clocks_per_frame(void) const {
		return	m_vmode.pixels_per_frame();
	}
};

#endif
