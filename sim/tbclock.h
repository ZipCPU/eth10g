////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tbclock.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	TBCLOCK is a class originally developed for the VideoZIP project
//		as a helper class to give Verilator the ability to test across
//	multiple clock domains.  In particular, it helps the testb.h file
//	determine when the next clocking event will (should) occur.
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
#ifndef	TBCLOCK_H
#define	TBCLOCK_H

class	TBCLOCK	{
	unsigned long	m_increment_ps, m_now_ps, m_last_posedge_ps, m_ticks;

public:
	TBCLOCK(void) {
		m_increment_ps = 10000; // 10 ns;

		m_now_ps = m_increment_ps+1;
		m_last_posedge_ps = 0;
		m_ticks = 0;
	}

	TBCLOCK(unsigned long increment_ps) {
		init(increment_ps);
	}

	unsigned long ticks(void) { return m_ticks; }

	void	init(unsigned long increment_ps) {
		set_interval_ps(increment_ps);

		// Start with the clock low, waiting on a positive edge
		m_now_ps = m_increment_ps+1;
		m_last_posedge_ps = 0;
	}

	unsigned long	time_to_edge(void) {
		if (m_last_posedge_ps > m_now_ps) {
			unsigned long ul;

			// Should never happen
			fprintf(stderr, "Internal tbclock error in %s:%d\n",
				__FILE__, __LINE__);
			fprintf(stderr, "\tGuru meditation %ld, %ld, %ld\n",
				m_last_posedge_ps, m_increment_ps, m_now_ps);
			assert(0);

			ul = m_last_posedge_ps - m_now_ps;
			ul /= m_increment_ps;

			ul = m_now_ps + ul * m_increment_ps;
			return ul;
			// return m_now_ps + ul * m_increment_ps;
		} else if (m_last_posedge_ps + m_increment_ps > m_now_ps)
			// Next edge is a negative edge
			return m_last_posedge_ps + m_increment_ps - m_now_ps;
		else if (m_last_posedge_ps + 2*m_increment_ps > m_now_ps)
			// Next edge is a positive edge
			return m_last_posedge_ps + 2*m_increment_ps - m_now_ps;
		else {
			// Should never happen
			fprintf(stderr, "Internal error in %s:%d\n",__FILE__,
				__LINE__);
			fprintf(stderr, "\tGuru meditation %ld, %ld, %ld\n",
				m_last_posedge_ps, m_increment_ps, m_now_ps);
			assert(0);
			return 2*m_increment_ps;
		}
	}

	void	set_interval_ps(unsigned long interval_ps) {
		// Divide the clocks interval by two, so we can have a
		// period for raising the clock, and another for lowering
		// the clock.
		m_increment_ps = (interval_ps>>1)&-2l;
		assert(m_increment_ps > 0);
	}

	void	set_frequency_hz(unsigned long frequency_hz) {
		double	tmp = 1e12 / (double)frequency_hz;
		unsigned long tmp_interval = (unsigned long)tmp;

		m_increment_ps = (tmp_interval>>1)&-2l;
		// printf("SET FREQ = %f MHz = %ld ps\n", frequency_hz/1e6, tmp_interval);
		assert(m_increment_ps > 0);
	}

	int	advance(unsigned long itime) {
		// Should never skip clocks
		assert(itime <= m_increment_ps);

		m_now_ps += itime;

		if (m_now_ps >= m_last_posedge_ps + 2*m_increment_ps) {
			// Advance to the next positive edge, and return
			// a positive valued clock
			m_last_posedge_ps += 2*m_increment_ps;
			m_ticks++;
			return 1;
		} else if (m_now_ps >= m_last_posedge_ps + m_increment_ps) {
			// Negative half of the clock's duty cycle
			return 0;
		} else
			// Positive half of the clock's duty cycle
			return 1;
	}

	bool	rising_edge(void) {
		if (m_now_ps == m_last_posedge_ps)
			return true;
		return false;
	}

	bool	falling_edge(void) {
		if (m_now_ps == m_last_posedge_ps + m_increment_ps)
			return true;
		return false;
	}
};
#endif
