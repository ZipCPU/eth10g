////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	dbluartsim.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To forward a Verilator simulated UART link over a pair of
//		TCP/IP pipes.  This version goes beyond the capabilities of
//	the original UARTSIM by forwarding (control) bytes with the high bit
//	set to one TCP/IP port, and the (console) bytes with the high bit clear
//	to another TCP/IP port.
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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <poll.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <signal.h>
#include <ctype.h>
#include <assert.h>

#include "dbluartsim.h"

int	DBLUARTSIM::setup_listener(const int port) {
	struct	sockaddr_in	my_addr;
	int	skt;

	signal(SIGPIPE, SIG_IGN);

	if (m_debug) printf("Listening on port %d\n", port);

	skt = socket(AF_INET, SOCK_STREAM, 0);
	if (skt < 0) {
		perror("ERR: Could not allocate socket: ");
		exit(EXIT_FAILURE);
	}

	// Set the reuse address option
	{
		int optv = 1, er;
		er = setsockopt(skt, SOL_SOCKET, SO_REUSEADDR, &optv, sizeof(optv));
		if (er != 0) {
			perror("ERR: SockOpt Err:");
			exit(EXIT_FAILURE);
		}
	}

	memset(&my_addr, 0, sizeof(struct sockaddr_in)); // clear structure
	my_addr.sin_family = AF_INET;
	// Use *all* internet ports to this computer, allowing connections from
	// any/every one of them.
	my_addr.sin_addr.s_addr = htonl(INADDR_ANY);
	my_addr.sin_port = htons(port);

	if (bind(skt, (struct sockaddr *)&my_addr, sizeof(my_addr))!=0) {
		perror("ERR: BIND FAILED:");
		exit(EXIT_FAILURE);
	}

	if (listen(skt, 1) != 0) {
		perror("ERR: Listen failed:");
		exit(EXIT_FAILURE);
	}

	return skt;
}

DBLUARTSIM::DBLUARTSIM(const int port, const bool copy_to_stdout)
		: m_copy(copy_to_stdout) {
	m_debug = false;
	m_con = m_cmd = -1;
	m_skt = setup_listener(port);
	m_console = setup_listener(port+1);
	m_rxpos = m_cmdpos = m_conpos = m_ilen = 0;
	m_started_flag = false;
	setup(25);	// Set us up for (default) 8N1 w/ a baud rate of CLK/25
	m_rx_baudcounter = 0;
	m_tx_baudcounter = 0;
	m_rx_state = RXIDLE;
	m_tx_state = TXIDLE;
	m_cllen = 0;
}

void	DBLUARTSIM::kill(void) {
	// Close any active connection
	if (m_con >= 0)	    {
		const	char	*SIM_CLOSED = "\n[SIM] Connection-Closed\n";
		int	nr, nw;
		if (m_conpos > 0) {
			nw = send(m_con,m_conbuf, m_conpos, 0);
		}
		nw = write(m_con, SIM_CLOSED, strlen(SIM_CLOSED));
		if (nw > 0) {
			shutdown(m_con, SHUT_WR);
			while(1) {
				char	buf[512];

				nr = ::read(m_con, buf, sizeof(buf));
				if (nr <= 0)
					break;
			} // close(m_con);
		}
	}
	if (m_skt >= 0)     close(m_skt);
	if (m_console >= 0) close(m_console);
	if (m_cmd >= 0) {
		int	nr = 0;
		if (m_cmdpos > 0)
			nr = send(m_cmd,m_cmdbuf, m_cmdpos, 0);
		shutdown(m_cmd, SHUT_WR);
		do {
			char	buf[512];

			nr = ::read(m_cmd, buf, sizeof(buf));
		} while(nr > 0);

		// close(m_cmd);
	}

	m_con     = -1;
	m_skt     = -1;
	m_console = -1;
	m_cmd     = -1;
}

void	DBLUARTSIM::setup(unsigned isetup) {
	if (isetup != m_setup) {
		m_setup = isetup;
		m_baud_counts = (isetup & 0x0ffffff);
		m_nbits   = 8-((isetup >> 28)&0x03);
		m_nstop   =((isetup >> 27)&1)+1;
		m_nparity = (isetup >> 26)&1;
		m_fixdp   = (isetup >> 25)&1;
		m_evenp   = (isetup >> 24)&1;
	}
}

void	DBLUARTSIM::poll_accept(void) {
	struct	pollfd	pb[2];
	int	npb = 0;

	// Check if we need to accept any connections
	if (m_cmd < 0) {
		pb[npb].fd = m_skt;
		pb[npb].events = POLLIN;
		npb++;
	}

	if (m_con < 0) {
		pb[npb].fd = m_console;
		pb[npb].events = POLLIN;
		npb++;
	}

	if (npb > 0) {
		int	pr;
		pr = poll(pb, npb, 0);

		assert(pr >= 0);

		if (pr > 0) for(int k=0; k<npb; k++) {
			if ((pb[k].revents & POLLIN)==0) {
				// printf("Not #%d\n", k);
				continue;
			}
			if (pb[k].fd == m_skt) {
				m_cmd = accept(m_skt, 0, 0);

				if (m_cmd < 0)
					perror("CMD Accept failed:");
				else printf("Accepted CMD connection\n");
			} else if (pb[k].fd == m_console) {
				m_con = accept(m_console, 0, 0);
				if (m_con < 0)
					perror("CON Accept failed:");
				else printf("Accepted CON connection\n");
			}
		}
	}

	// End of trying to accept more connections
}

void	DBLUARTSIM::poll_read(void) {
	struct	pollfd	pb[2];
	int		npb = 0, r;

	if (m_cmd >= 0) {
		pb[npb].fd = m_cmd;
		pb[npb].events = POLLIN;
		npb++;
	} if (m_con >= 0) {
		pb[npb].fd = m_con;
		pb[npb].events = POLLIN;
		npb++;
	}

	if (npb == 0)
		return;

	r = poll(pb, npb, 0);
	if (r < 0)
		perror("Polling error:");
	else if (r == 0)
		return;

	// printf("POLL = %d\n", r);
	for(int i=0; i<npb; i++) {
		if (pb[i].revents & POLLIN) {
			int	nr;
			nr =recv(pb[i].fd, &m_rxbuf[m_ilen],
					sizeof(m_rxbuf)-m_ilen,
					MSG_DONTWAIT);

			if (pb[i].fd == m_cmd) {
				for(int j=0; j<nr; j++) {
					m_cmdline[m_cllen] = m_rxbuf[j+m_ilen];
					if (m_cmdline[m_cllen] != '\r') {
						if (m_cmdline[m_cllen] == '\n'){
							m_cmdline[m_cllen]='\0';
							printf("< %s\n", m_cmdline);
							m_cllen=0;
						} else
							m_cllen++;
					} if (m_cllen >= 64) {
						m_cmdline[m_cllen+1] = '\0';
						printf("< %s\n", m_cmdline);
						m_cllen = 0;
					}
					
					m_rxbuf[j+m_ilen] |= 0x80;
				} m_cmdline[m_cllen] = '\0';


				if (nr <= 0) {
					m_cmdline[m_cllen] = '\0';
					printf("< %s [CLOSED]\n", m_cmdline);
					m_cllen = 0;
				}
			} if (nr > 0) {
				m_ilen += nr;
				if (m_ilen == sizeof(m_rxbuf))
					break;
			} else if (nr <= 0) {
				close(pb[i].fd);
				if (pb[i].fd == m_cmd)
					m_cmd = -1;
				else // if (pb[i].fd == m_con)
					m_con = -1;
			}
		}
	} m_rxpos = 0;
}

void	DBLUARTSIM::received(const char ch) {
	if (ch & 0x80) {
		m_cmdbuf[m_cmdpos++] = ch & 0x7f;
	} else
		m_conbuf[m_conpos++] = ch & 0x7f;
	if ((m_cmdpos>0)&&((m_cmdbuf[m_cmdpos-1] == '\n')
				||(m_cmdpos >= DBLPIPEBUFLEN-2))) {
		int	snt = 0;
		if (m_cmd >= 0)
			snt = send(m_cmd,m_cmdbuf, m_cmdpos, 0);
		else
			snt = m_cmdpos;
		if (snt < 0) {
			printf("Closing CMD socket\n");
			close(m_cmd);
			m_cmd = -1;
			snt = 0;
		} // else printf("%d/%d bytes returned\n", snt, m_cmdpos);
		m_cmdbuf[m_cmdpos] = '\0';
		if (m_copy) printf("> %s", m_cmdbuf);
		if (snt < m_cmdpos) {
			fprintf(stderr, "CMD: Only sent %d bytes of %d!\n",
				snt, m_cmdpos);
		}
		m_cmdpos = 0;
	}

	if ((m_con >= 0)&&(m_conpos > 0)) {
		int	snt = 0;
		snt = send(m_con, &m_conbuf[m_conpos-1], 1, 0);
		if (snt < 0) {
			printf("Closing CONsole socket\n");
			close(m_con);
			m_con = -1;
			snt = 0;
		} if (snt < 1) {
			fprintf(stderr, "CON: no bytes sent!\n");
		} m_conpos = 0;
	} if ((m_conpos>0)&&((m_conbuf[m_conpos-1] == '\n')
				||(m_conpos >= DBLPIPEBUFLEN-2))) {
		m_conbuf[m_conpos] = '\0';
		printf("%s", m_conbuf);
		m_conpos = 0;
	}
}

int	DBLUARTSIM::next(void) {
	// If our transmit buffer is empty, see if we can
	// fill it.
	if (m_ilen == 0)
		poll_read();
	if (m_ilen <= 0)
		return -1;

	int	nval;
	nval = m_rxbuf[m_rxpos++];
	m_ilen--;

	return nval & 0x0ff;
}

int	DBLUARTSIM::tick(int i_tx) {
	int	o_rx = 1;

	poll_accept();

	if ((!i_tx)&&(m_last_tx))
		m_rx_changectr = 0;
	else	m_rx_changectr++;
	m_last_tx = i_tx;

	if (m_rx_state == RXIDLE) {
		if (!i_tx) {
			m_rx_state = RXDATA;
			m_rx_baudcounter =m_baud_counts+m_baud_counts/2-1;
			m_rx_baudcounter -= m_rx_changectr;
			m_rx_busy    = 0;
			m_rx_data    = 0;
		}
	} else if (m_rx_baudcounter <= 0) {
		if (m_rx_busy >= (1<<(m_nbits+m_nparity+m_nstop-1))) {
			char	ch;
			m_rx_state = RXIDLE;
			ch = (m_rx_data >> (32-m_nbits-m_nstop-m_nparity))&0x0ff;
			received(ch);
		} else {
			m_rx_busy = (m_rx_busy << 1)|1;
			// Low order bit is transmitted first, in this
			// order:
			//	Start bit (1'b1)
			//	bit 0
			//	bit 1
			//	bit 2
			//	...
			//	bit N-1
			//	(possible parity bit)
			//	stop bit
			//	(possible secondary stop bit)
			m_rx_data = ((i_tx&1)<<31) | (m_rx_data>>1);
		} m_rx_baudcounter = m_baud_counts-1;
	} else
		m_rx_baudcounter--;

	if (m_tx_state == TXIDLE) {
		int	ch;
		ch = next();
		if (ch >= 0) {
			// printf("NEXTV: ch = %x\n", ch);
			m_tx_data = (-1<<(m_nbits+m_nparity+1))
				// << nstart_bits
				|((ch<<1)&0x01fe);
			if (m_nparity) {
				int	p;

				// If m_nparity is set, we need to then
				// create the parity bit.
				if (m_fixdp)
					p = m_evenp;
				else {
					p = (m_tx_data >> 1)&0x0ff;
					p = p ^ (p>>4);
					p = p ^ (p>>2);
					p = p ^ (p>>1);
					p &= 1;
					p ^= m_evenp;
				}
				m_tx_data |= (p<<(m_nbits+m_nparity));
			}
			m_tx_busy = (1<<(m_nbits+m_nparity+m_nstop+1))-1;
			m_tx_state = TXDATA;
			o_rx = 0;
			m_tx_baudcounter = m_baud_counts-1;
		}
	} else if (m_tx_baudcounter <= 0) {
		m_tx_data >>= 1;
		m_tx_busy >>= 1;
		if (!m_tx_busy)
			m_tx_state = TXIDLE;
		else
			m_tx_baudcounter = m_baud_counts-1;
		o_rx = m_tx_data&1;
	} else {
		m_tx_baudcounter--;
		o_rx = m_tx_data&1;
	}

	return o_rx;
}
