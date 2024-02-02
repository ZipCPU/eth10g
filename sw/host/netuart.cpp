////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/netuart.cpp
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
//
// }}}
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <termios.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <string.h>
#include <poll.h>
#include <signal.h>
#include <ctype.h>
#include <assert.h>
#include <errno.h>

#include "regdefs.h"
#include "port.h"

#ifndef	BAUDRATE
#define	BAUDRATE	115200
#endif

#define	NO_WAITING	0
#define	FOREVER		-1

void	sigstop(int v) {
	fprintf(stderr, "SIGSTOP!!\n");
	exit(0);
}
void	sighup(int v) {
	fprintf(stderr, "SIGHUP!!\n");
	exit(0);
}
void	sigint(int v) {
	fprintf(stderr, "SIGINT!!\n");
	exit(0);
}
void	sigsegv(int v) {
	fprintf(stderr, "SIGSEGV!!\n");
	exit(0);
}
void	sigbus(int v) {
	fprintf(stderr, "SIGBUS!!\n");
	exit(0);
}
void	sigpipe(int v) {
	fprintf(stderr, "SIGPIPE!!\n");
	exit(0);
}

int	setup_listener(const int port) {
	int	skt;
	struct  sockaddr_in     my_addr;

	printf("Listening on port %d\n", port);

	skt = socket(AF_INET, SOCK_STREAM, 0);
	if (skt < 0) {
		perror("Could not allocate socket: ");
		exit(-1);
	}

	// Set the reuse address option
	{
		int optv = 1, er;
		er = setsockopt(skt, SOL_SOCKET, SO_REUSEADDR, &optv, sizeof(optv));
		if (er != 0) {
			perror("SockOpt Err:");
			exit(-1);
		}
	}

	memset(&my_addr, 0, sizeof(struct sockaddr_in)); // clear structure
	my_addr.sin_family = AF_INET;
	my_addr.sin_addr.s_addr = htonl(INADDR_ANY);
	my_addr.sin_port = htons(port);

	if (bind(skt, (struct sockaddr *)&my_addr, sizeof(my_addr))!=0) {
		perror("BIND FAILED:");
		exit(-1);
	}

	if (listen(skt, 1) != 0) {
		perror("Listen failed:");
		exit(-1);
	}

	return skt;
}

class	LINBUFS {
public:
	char	m_iline[512], m_oline[512];
	char	m_buf[256];
	int	m_ilen, m_olen;
	int	m_fd;
	bool	m_connected;

	LINBUFS(void) {
		m_ilen = 0; m_olen = 0; m_connected = false; m_fd = -1;
	}

	void	close(void) {
		if (!m_connected) {
			m_fd = -1;
			return;
		} if (m_fd < 0) {
			m_connected = false;
			return;
		}
		::close(m_fd);
		m_fd = -1;
		m_connected = false;
	}

	int	read(void) {
		return ::read(m_fd, m_buf, sizeof(m_buf));
	}

	void	accept(const int skt) {
		m_fd = ::accept(skt, 0, 0);
		if (m_fd < 0) {
			perror("CMD Accept failed!  O/S Err:");
			exit(EXIT_FAILURE);
		} m_connected = (m_fd >= 0);
	}

	int	write(int fd, int ln, int mask = 0) {
		int	pos = 0, nw;

		if (mask) {
			for(int i=0; i<ln; i++)
				m_buf[i] |= mask;
		}

		do {
			nw = ::write(fd, &m_buf[pos], ln-pos);

			if ((nw < 0)&&(errno == EAGAIN)) {
				nw = 0;
				usleep(10);
			} else if (nw < 0) {
				fprintf(stderr, "ERR: %4d\n", errno);
				perror("O/S Err: ");
				// exit(EXIT_FAILURE);
				break;
			} else if (nw == 0) {
				// TTY device has closed our connection
				fprintf(stderr, "TTY device has closed\n");
				exit(EXIT_SUCCESS);
				break;
			}
			pos += nw;
		} while(pos < ln);

		return pos;
	}

	void	print_in(FILE *fp, int ln, const char *prefix = NULL) {
		// lbcmd.print_in(ncmd, (lbcmd.m_fd>=0)?"> ":"# ");
		assert(ln > 0);
		for(int i=0; i<ln; i++) {
			m_iline[m_ilen++] = m_buf[i];
			bool	nl, fullline;
			nl = (m_iline[m_ilen-1] == '\n');
			nl=(nl)||(m_iline[m_ilen-1] == '\r');

			fullline = ((unsigned)m_ilen >= sizeof(m_iline)-1);

			if ((nl)||(fullline)) {
				if ((unsigned)m_ilen >= sizeof(m_iline)-1)
					m_iline[m_ilen] = '\0';
				else
					m_iline[m_ilen-1] = '\0';
				if (m_ilen > 1)
					fprintf(fp, "%s%s\n",
						(prefix)?prefix:"", m_iline);
				m_ilen = 0;
			}
		}
	}

	void	print_out(FILE *fp, int ln, const char *prefix = NULL) {
		for(int i=0; i<ln; i++) {
			m_oline[m_olen++] = m_buf[i] & 0x07f;
			assert(m_buf[i] != '\0');
			if ((m_oline[m_olen-1]=='\n')
					||(m_oline[m_olen-1]=='\r')
					||((unsigned)m_olen
						>= sizeof(m_oline)-1)) {
				if ((unsigned)m_olen >= sizeof(m_oline)-1)
					m_oline[m_olen] = '\0';
				else
					m_oline[m_olen-1] = '\0';
				if (m_olen > 1)
					fprintf(fp,"%s%s\n",
						(prefix)?prefix:"", m_oline);
				m_olen = 0;
			}
		}
	}

	void	flush_out(FILE *fp, const char *prefix = NULL) {
		if(m_olen > 0) {
			m_oline[m_olen] = '\0';
			fprintf(fp, "%s%s\n", (prefix)?prefix:"", m_oline);
			m_olen = 0;
		}
	}
};

int	main(int argc, char **argv) {
	// First, accept a network connection
	int	skt = setup_listener(FPGAPORT),
		console = setup_listener(FPGAPORT+1);
	int	tty;
	bool	done = false;

	// Disable signals
	// {{{
	signal(SIGSTOP, sigstop);
	signal(SIGBUS, sigbus);
	signal(SIGSEGV, sigsegv);
	signal(SIGPIPE, SIG_IGN);
	signal(SIGINT, sigint);
	signal(SIGHUP, sighup);
	// }}}

	// Open a connection to the TTY port
	// {{{
	if ((argc > 1)&&(NULL != strstr(argv[1], "/ttyUSB"))) {
		// printf("Opening %s\n", argv[1]);
		tty = open(argv[1], O_RDWR | O_NONBLOCK);
		if (tty < 0) {
		printf("Could not open tty\n");
			fprintf(stderr, "Could not open tty device, %s\n", argv[1]);
			perror("O/S Err:");
			exit(-1);
		}
	} else if (argc == 1) {
		const	char *deftty = "/dev/ttyUSB2";
		// printf("Opening %s\n", deftty);
		tty = open(deftty, O_RDWR | O_NONBLOCK);
		if (tty < 0) {
			fprintf(stderr, "Attempted to guess the TTY, but could not open %s\n", deftty);
			perror("O/S Err:");
			exit(-1);
		}
	} else {
		printf("Unknown argument: %s\n", argv[1]);
		exit(-2);
	}

	if (tty < 0) {
		printf("Could not open tty\n");
		perror("O/S Err:");
		exit(-1);
	}
	// }}}

	// Configure the BAUDRATE, parity, stop bits, etc.
	// {{{
	if (isatty(tty)) {
		struct	termios	tb;

		printf("Setting up TTY for %d Baud\n", BAUDRATE);
		if (tcgetattr(tty, &tb) < 0) {
			printf("Could not get TTY attributes\n");
			perror("O/S Err:");
			exit(-2);
		}

		cfmakeraw(&tb); // Sets no parity, 8 bits, one stop bit
		tb.c_cflag &= (~(CRTSCTS)); // Sets no parity, 8 bit
		tb.c_cflag &= (~(CSTOPB)); // One stop bit

		// 8-bit
		tb.c_cflag &= ~(CSIZE);
		tb.c_cflag |= CS8;
		if (BAUDRATE == 2400) {
			// 2400 Baud
			cfsetispeed(&tb, B2400);
			cfsetospeed(&tb, B2400);
		} else if (BAUDRATE == 9600) {
			// 9.6 kBaud
			cfsetispeed(&tb, B9600);
			cfsetospeed(&tb, B9600);
		} else if (BAUDRATE == 19200) {
			// 19.2 kBaud
			cfsetispeed(&tb, B19200);
			cfsetospeed(&tb, B19200);
		} else if (BAUDRATE == 38400) {
			// 38.4 kBaud
			cfsetispeed(&tb, B38400);
			cfsetospeed(&tb, B38400);
		} else if (BAUDRATE == 57600) {
			// 57.6 kBaud
			cfsetispeed(&tb, B57600);
			cfsetospeed(&tb, B57600);
		} else if (BAUDRATE == 115200) {
			// 115.2kBaud
			cfsetispeed(&tb, B115200);
			cfsetospeed(&tb, B115200);
		} else if (BAUDRATE == 1000000) {
			// 1 MBaud
			cfsetispeed(&tb, B1000000);
			cfsetospeed(&tb, B1000000);
		} else if (BAUDRATE == 2000000) {
			// 2 MBaud
			cfsetispeed(&tb, B2000000);
			cfsetospeed(&tb, B2000000);
		} else if (BAUDRATE == 2500000) {
			// 2.5 MBaud
			cfsetispeed(&tb, B2500000);
			cfsetospeed(&tb, B2500000);
		} else if (BAUDRATE == 3000000) {
			// 2 MBaud
			cfsetispeed(&tb, B3000000);
			cfsetospeed(&tb, B3000000);
		} else if (BAUDRATE == 3000000) {
			// 3.5 MBaud
			cfsetispeed(&tb, B3500000);
			cfsetospeed(&tb, B3500000);
		} else if (BAUDRATE == 4000000) {
			// 4 MBaud
			cfsetispeed(&tb, B4000000);
			cfsetospeed(&tb, B4000000);
		} else {
			fprintf(stderr, "Unsupported baud rate: %d Hz\n", BAUDRATE);
			exit(EXIT_FAILURE);
		}

		if (tcsetattr(tty, TCSANOW, &tb) < 0) {
			printf("Could not set any TTY attributes\n");
			perror("O/S Err:");
		}
		tcflow(tty, TCOON);
	}
	// }}}

	LINBUFS	lbcmd, lbcon;
	while(!done) {
		struct	pollfd	p[4];
		int	pv, nfds;

		//
		// Poll to see if we have any events to examine
		// {{{
		nfds = 0;

		p[nfds].fd = tty;
		p[nfds].events = POLLIN | POLLERR;
		nfds++;

		if (lbcmd.m_connected) {
			p[nfds].fd = lbcmd.m_fd;
			p[nfds].events = POLLIN | POLLRDHUP | POLLERR;
			nfds++;
		} else {
			p[nfds].fd = skt;
			p[nfds].events = POLLIN | POLLERR;
			nfds++;
		}

		if (lbcon.m_connected) {
			p[nfds].fd = lbcon.m_fd;
			p[nfds].events = POLLIN | POLLRDHUP | POLLERR;
			nfds++;
		} else {
			p[nfds].fd = console;
			p[nfds].events = POLLIN | POLLERR;
			nfds++;
		}

		if ((pv=poll(p, nfds, FOREVER)) < 0) {
			perror("Poll Failed!  O/S Err:");
			exit(-1);
		}
		// }}}

		//
		//
		// Now we evaluate what just happened
		//
		//

		// Start by flusing everything on the TTY channel
		// {{{
		if (p[0].revents & POLLIN) {
			char	rawbuf[256];
			int nr = read(tty, rawbuf, sizeof(rawbuf));
			if (nr == 0) {
				fprintf(stderr, "TTY device has closed\n");
				exit(EXIT_SUCCESS);
			} else if (nr < 0) {
				fprintf(stderr, "ERR: Could not read from TTY\n");
				perror("O/S Err:");
				exit(EXIT_FAILURE);
			} else while(nr > 0) {
				int	ncmd = 0, ncon = 0;
				for(int i=0; i<nr; i++) {
					if (rawbuf[i] & 0x80)
						lbcmd.m_buf[ncmd++] = rawbuf[i] & 0x07f;
					else
						lbcon.m_buf[ncon++] = rawbuf[i];
				}
				if ((lbcmd.m_fd >= 0)&&(ncmd>0)) {
					int	nw;
					nw = lbcmd.write(lbcmd.m_fd, ncmd);
					if(nw != ncmd) {
					// This fails when the other end resets
					// the connection.  Thus, we'll just
					// kindly close the connection and skip
					// the assert that once was at the end.
					lbcmd.close();
					}
				}

				if ((lbcon.m_fd >= 0)&&(ncon>0)) {
					int	nw;
					nw = lbcon.write(lbcon.m_fd, ncon);
					if(nw != ncon) {
					// This fails when the other end resets
					// the connection.  Thus, we'll just
					// kindly close the connection and skip
					// the assert that once was at the end.
					lbcon.close();
					}
				}

				if (ncmd > 0)
					lbcmd.print_in(stdout, ncmd, (lbcmd.m_fd>=0)?"> ":"# ");
				if (ncon > 0)
					lbcon.print_in(stdout, ncon);
				nr = read(tty, rawbuf, sizeof(rawbuf));
			}
		} else if (p[0].revents) {
			fprintf(stderr, "ERR: UNKNOWN TTY EVENT: %d\n", p[0].revents);
			perror("O/S Err?");
			exit(EXIT_FAILURE);
		}
		// }}}

		if (p[1].revents & POLLIN) {
			if (p[1].fd == skt) {
				lbcmd.accept(skt);
			} else { // p[1].fd == lbcmd.m_fd
				int nr = lbcmd.read();
				if (nr == 0) {
					lbcmd.flush_out(stdout, "< ");
					// printf("Disconnect\n");
					lbcmd.close();
				} else if (nr > 0) {
					// printf("%d read from SKT\n", nr);
					lbcmd.write(tty, nr, 0x80);
					lbcmd.print_out(stdout, nr, "< ");
				}
			}
		}

		if (p[2].revents & POLLIN) {
			if (p[2].fd == console) {
				lbcon.accept(console);
				printf("Accepted a console connection\n");
			} else { // p[1].fd == lbcon.m_fd
				int nr = lbcon.read();
				if (nr == 0) {
					lbcon.flush_out(stdout);
					lbcon.close();
				} else if (nr > 0) {
					lbcon.write(tty, nr, 0x0);
					lbcon.print_out(stdout, nr);
				}
			}
		}
	}

	// Close up
	// {{{
	printf("Closing our sockets\n");
	close(console);
	close(skt);
	// }}}
}

