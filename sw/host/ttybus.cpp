////////////////////////////////////////////////////////////////////////////////
//
// Filename:	ttybus.cpp
// {{{
// Project:	Demonstration SONAR project
//
// Purpose:	This is the C++ program on the command side that will interact
//		with a UART on an FPGA, to command the WISHBONE on that same
//	FPGA to ... whatever we wish to command it to do.
//
//	This code does not run on an FPGA, is not a test bench, neither is it a
//	simulator.  It is a portion of a command program for commanding an FPGA.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022, Symbiotic EDA, Gmbh
// {{{
// This file is part of the demonstration SONAR project.  The demonstration
// SONAR project is proprietary to Symbiotic EDA, Gmbh.  It may not be
// redistributed without the express permission of an authorized representative
// of Symbiotic EDA, Gmbh.
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <termios.h>
#include <netinet/in.h>
#include <netdb.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <arpa/inet.h> 
#include <assert.h> 
#include <strings.h> 
#include <poll.h> 
#include <ctype.h> 

#include "ttybus.h"

#define	TTYC_IDLE	'0'
#define	TTYC_BUSY	'1'
#define	TTYC_WRITE	'2'
#define	TTYC_RESET	'3'
#define	TTYC_INT	'4'
#define	TTYC_ERR	'5'

const	unsigned TTYBUS::MAXRDLEN = 1024;
const	unsigned TTYBUS::MAXWRLEN = 32;

// #define	DBGPRINTF	printf
// #define	DBGPRINTF	filedump
#ifndef	DBGPRINTF
#define	DBGPRINTF	null
#else
#warning "TTYBUS DEBUG IS TURNED ON"
#endif

// }}}
static	void	null(...) {}

#include <stdarg.h> // replaces the (defunct) varargs.h include file
__attribute__ ((unused))
static	void	filedump(const char *fmt, ...) {
	static	FILE *dbgfp = NULL;
	va_list	args;

	if (!dbgfp) {
		dbgfp = fopen("debug.txt", "w");
		// fprintf(dbgfp, "\n\n\n-----------------------------\n");
		// fprintf(dbgfp, "     NEW TRANSACTION \n");
		// fprintf(dbgfp, "-----------------------------\n");
	}
	va_start(args, fmt);
	vfprintf(dbgfp, fmt, args);
	va_end(args);
	fflush(dbgfp);

	// If you want the debug output to go to stderr as well, you can
	// uncomment the next couple of lines
	// va_start(args, fmt);
	// vfprintf(stderr, fmt, args);
	// va_end(args);
}

char	TTYBUS::charenc(const int sixbitval) const {
	if (sixbitval < 10)
		return '0' + sixbitval;
	else if (sixbitval < 10+26)
		return 'A' - 10 + sixbitval;
	else if (sixbitval < 10+26+26)
		return 'a' - 10 - 26 + sixbitval;
	else if (sixbitval == 0x3e)
		return '@';
	else if (sixbitval == 0x3f)
		return '%';

	fprintf(stderr, "INTERNAL ERR: SIXBITVAL isn\'t!!!! sixbitval = %08x\n", sixbitval);
	assert((sixbitval & (~0x03f))==0);
	return 0;
}

unsigned	TTYBUS::chardec(const char b) const {
	if ((b >= '0')&&(b <= '9'))
		return b-'0';
	else if ((b >= 'A')&&(b <= 'Z'))
		return b-'A'+10;
	else if ((b >= 'a')&&(b <= 'z'))
		return b-'a'+36;
	else if (b == '@')
		return 0x03e;
	else if (b == '%')
		return 0x03f;
	else
		return 0x0100; // ERR -- invalid code
}

int	TTYBUS::lclreadcode(char *buf, int len) {
	char	*sp, *dp;
	int	nr, ret;

	nr = m_dev->read(buf, len);
	m_total_nread += nr;
	ret = nr; sp = buf; dp = buf;
	for(int i=0; i<nr; i++) {
		if (chardec(*sp)&(~0x3f)) {
			ret--;	// Skip this value, not a valid codeword
			sp++;
		} else {
			*sp++ = *dp++;
		}
	} return ret;
}

/*
 * bufalloc
 *
 * Allocate a buffer of at least length (len).  This is similar to realloc().
 *
 */
void	TTYBUS::bufalloc(int len) {
	if ((m_buf)&&(m_buflen >= len))
		return;
	if (m_buf)
		delete[] m_buf;
	m_buflen = (len&(-0x3f))+0x40;
	m_buf = new char[m_buflen];
}

void	TTYBUS::encode(const int hb, const BUSW val, char *buf) const {
	buf[0] = charenc( (hb<<2)|((val>>30)&0x03) );
	buf[1] = charenc( (val>>24)&0x3f);
	buf[2] = charenc( (val>>18)&0x3f);
	buf[3] = charenc( (val>>12)&0x3f);
	buf[4] = charenc( (val>> 6)&0x3f);
	buf[5] = charenc( (val    )&0x3f);
}

unsigned	TTYBUS::decodestr(const char *buf) const {
	unsigned	r;

	r = chardec(buf[0]) & 0x03;
	r = (r<<6) | (chardec(buf[1]) & 0x03f);
	r = (r<<6) | (chardec(buf[2]) & 0x03f);
	r = (r<<6) | (chardec(buf[3]) & 0x03f);
	r = (r<<6) | (chardec(buf[4]) & 0x03f);
	r = (r<<6) | (chardec(buf[5]) & 0x03f);

	return r;
}

int	TTYBUS::decodehex(const char hx) const {
	if ((hx >= '0')&&(hx <= '9'))
		return hx-'0';
	else if ((hx >= 'A')&&(hx <= 'Z'))
		return hx-'A'+10;
	else if ((hx >= 'a')&&(hx <= 'z'))
		return hx-'a'+10;
	else
		return 0;
}

/*
 * writeio
 *
 * Write a single value to the debugging interface
 */
void	TTYBUS::writeio(const BUSW a, const BUSW v) {

	writev(a, 0, 1, &v);
	m_lastaddr = a; m_addr_set = true;
}

/*
 * writev
 *
 * This internal write function.  This writes a buffer of information to our
 * interface, and the place to study how a write works.
 *
 * Parameters:
 *	a	is the address to write to
 *	p	=1 to increment address, 0 otherwise
 *	len	The number of values to write to the bus
 *	buf	A memory pointer to the information to write
 *
 * Notice that this routine can only write complete 32-bit words.  It doesn't
 * really have any 8-bit byte support, although you might be able to create such
 * by readio()'ing a word, modifying it, and then calling writeio() to write the
 * modified word back.
 */
void	TTYBUS::writev(const BUSW a, const int p, const int len, const BUSW *buf) {
	char	*ptr;
	int	nw = 0;

	// We'll never be called with more than MAXWRLEN words to write at once.
	// This is a configurable option length, set at the top of this file.
	// (currently set at 32, but subject to change ...)  This is important,
	// as the return channel *must* be capable of holding at least this many
	// acknowledgments in its buffer.
	//
	// assert(len <= MAXWRLEN);

	// Allocate a buffer of six bytes per word, one for addr, plus
	// six more
	bufalloc((len+2)*6);

	DBGPRINTF("WRITEV(%08x,%d,#%d,0x%08x ...)\n", a, p, len, buf[0]);
	// Encode the address
	ptr = encode_address(a);
	m_lastaddr = a; m_addr_set = true;

	while(nw < len) {
		int	ln = len-nw;
		if ((unsigned)ln > MAXWRLEN)
			ln = MAXWRLEN;

		DBGPRINTF("WRITEV-SUB(%08x%s,#%d,&buf[%d])\n", a+nw, (p)?"++":"", ln, nw);
		for(int i=0; i<ln; i++) {
			BUSW	val = buf[nw+i];

			int	caddr = 0;
			// Let's try compression
			for(int i=1; i<256; i++) {
				unsigned	tstaddr;
				tstaddr = (m_wraddr - i) & 0x0ff;
				if ((!m_wrloaded)&&(tstaddr > (unsigned)m_wraddr))
					break;
				if (m_writetbl[tstaddr] == val) {
					caddr = ( m_wraddr- tstaddr ) & 0x0ff;
					break;
				}
			}

		/*
		if (caddr != 0)
			DBGPRINTF("WR[%08x] = %08x (= TBL[%4x] <= %4x)\n", m_lastaddr, val, caddr, m_wraddr);
		else
			DBGPRINTF("WR[%08x] = %08x\n", m_lastaddr, val);
		*/

			if (caddr != 0) {
				*ptr++ = charenc( (((caddr>>6)&0x03)<<1) + (p?1:0) + 0x010);
				*ptr++ = charenc(    caddr    &0x3f    );
			
			} else {
				// For testing, let's start just doing this the hard way
				*ptr++ = charenc( (((val>>30)&0x03)<<1) + (p?1:0) + 0x018);
				*ptr++ = charenc( (val>>24)&0x3f);
				*ptr++ = charenc( (val>>18)&0x3f);
				*ptr++ = charenc( (val>>12)&0x3f);
				*ptr++ = charenc( (val>> 6)&0x3f);
				*ptr++ = charenc( (val    )&0x3f);

				m_writetbl[m_wraddr++] = val;
				m_wraddr &= 0x0ff;
				if (m_wraddr == 0) {
					m_wrloaded = true;
				}
			}

			if (p == 1) m_lastaddr+=4;
		}
		// *ptr++ = charenc(0x2e);
		if (ln == len-nw)
			*ptr++ = '\n';
		*ptr = '\0';
		m_dev->write(m_buf, ptr-m_buf);
		DBGPRINTF(">> %s\n", m_buf);

		readidle();

		nw += ln;
		ptr = m_buf;
	}
	DBGPRINTF("WR: LAST ADDRESS LEFT AT %08x\n", m_lastaddr);

	// Need to clear the incoming queue ... if there's anything there.
	// We could do a ...
	//	readacks(len);
	// to clear a known number of acks (up to half the length of our buffer
	// which we can let just sit for speed ...), or we could do a ...
	//	readtilidle(void);
	// Then, upon startup we could also start with a readtilidle(); command.
	// This would help to clear out the problems between programs, where
	// one program doesn't finish reading, and the next gets a confusing
	// message.
	readidle();
}

/*
 * writez
 *
 * Write a buffer of values to a single address.
 */
void	TTYBUS::writez(const BUSW a, const int len, const BUSW *buf) {
	writev(a, 0, len, buf);
}

/*
 * writei
 *
 * Write a buffer of values to a memory range.  Unlike writez, this function
 * increments the address pointer after every memory write.
 */
void	TTYBUS::writei(const BUSW a, const int len, const BUSW *buf) {
	writev(a, 1, len, buf);
}

/*
 * readio
 *
 * Read a single value from the bus.
 *
 * If the bus returns an error, this routine will print a comment and throw
 * the error up the chain.  If the address of the value read doesn't match
 * the address requested (an internal check), then an error message will be
 * sent to the log file and the interface will exit with an error condition.
 * This should only happen if there are bugs in the interface, and hopefully
 * I've gotten rid of all of those.
 *
 */
TTYBUS::BUSW	TTYBUS::readio(const TTYBUS::BUSW a) {
	BUSW	v;

	// I/O reads are now the same as vector reads, but with a vector length
	// of one.
	DBGPRINTF("READIO(0x%08x)\n", a);
	try {
		readv(a, 0, 1, &v);
	} catch(BUSERR b) {
		DBGPRINTF("BUSERR trying to read %08x\n", a);
		throw BUSERR(a);
	}

	if (m_lastaddr != a) {
		DBGPRINTF("LAST-ADDR MIS-MATCH: (RCVD) %08x != %08x (XPECTED)\n", m_lastaddr, a);
		m_addr_set = false;

		exit(-3);
	}

	return v;
}

/*
 * encode_address
 *
 * Creates a message to be sent across the bus with a new address value
 * in it.
 *
 */
char	*TTYBUS::encode_address(const TTYBUS::BUSW a) {
	TTYBUS::BUSW	addr = a>>2;
	char	*ptr = m_buf;

	// Double check that we are aligned
	if ((a&3)!=0) {
		throw BUSERR(a);
	}

	if ((m_addr_set)&&(a == m_lastaddr))
		return ptr;
	
	if (m_addr_set) {
		// Encode a difference address
		int	diffaddr = (a - m_lastaddr)>>2;
		ptr = m_buf;
		if ((diffaddr >= -32)&&(diffaddr < 32)) {
			*ptr++ = charenc(0x09);
			*ptr++ = charenc(diffaddr & 0x03f);
		} else if ((diffaddr >= -2048)&&(diffaddr < 2048)) {
			*ptr++ = charenc(0x0b);
			*ptr++ = charenc((diffaddr>>6) & 0x03f);
			*ptr++ = charenc( diffaddr     & 0x03f);
		} else if ((diffaddr >= -(1<<17))&&(diffaddr < (1<<17))) {
			*ptr++ = charenc(0x0d);
			*ptr++ = charenc((diffaddr>>12) & 0x03f);
			*ptr++ = charenc((diffaddr>> 6) & 0x03f);
			*ptr++ = charenc( diffaddr      & 0x03f);
		} else if ((diffaddr >= -(1<<23))&&(diffaddr < (1<<23))) {
			*ptr++ = charenc(0x0f);
			*ptr++ = charenc((diffaddr>>18) & 0x03f);
			*ptr++ = charenc((diffaddr>>12) & 0x03f);
			*ptr++ = charenc((diffaddr>> 6) & 0x03f);
			*ptr++ = charenc( diffaddr      & 0x03f);
		}
		*ptr = '\0';
		DBGPRINTF("DIF-ADDR: (%ld) \'%s\' encodes last_addr(0x%08x) %c %d(0x%08x)\n",
			ptr-m_buf, m_buf,
			m_lastaddr, (diffaddr<0)?'-':'+',
			diffaddr, diffaddr&0x0ffffffff);
	}

	{
		// Encode an absolute (low memory) address
		// Prefer absolute address encoding over differential encoding,
		// when both encodings encode the same address, and when both
		// encode the address in the same number of words
		if ((addr <= 0x03f)&&((ptr == m_buf)||(ptr >= &m_buf[2]))) {
			ptr = m_buf;
			*ptr++ = charenc(0x08);
			*ptr++ = charenc(addr);
		} else if((addr <= 0x0fff)&&((ptr == m_buf)||(ptr >= &m_buf[3]))) {
			DBGPRINTF("Setting ADDR.3 to %08x\n", addr);
			ptr = m_buf;
			*ptr++ = charenc(0x0a);
			*ptr++ = charenc((addr>> 6) & 0x03f);
			*ptr++ = charenc( addr      & 0x03f);
		} else if((addr <= 0x03ffff)&&((ptr == m_buf)||(ptr >= &m_buf[4]))) {
			DBGPRINTF("Setting ADDR.4 to %08x\n", addr);
			ptr = m_buf;
			*ptr++ = charenc(0x0c);
			*ptr++ = charenc((addr>>12) & 0x03f);
			*ptr++ = charenc((addr>> 6) & 0x03f);
			*ptr++ = charenc( addr      & 0x03f);
		} else if((addr <= 0x0ffffff)&&((ptr == m_buf)||(ptr >= &m_buf[5]))) {
			DBGPRINTF("Setting ADDR.5 to %08x\n", addr);
			ptr = m_buf;
			*ptr++ = charenc(0x0e);
			*ptr++ = charenc((addr>>18) & 0x03f);
			*ptr++ = charenc((addr>>12) & 0x03f);
			*ptr++ = charenc((addr>> 6) & 0x03f);
			*ptr++ = charenc( addr      & 0x03f);
		} else if (ptr == m_buf) { // Send our address prior to any read
			// ptr = m_buf;
			encode(0, addr, ptr);
			ptr+=6;
		}
	}

	*ptr = '\0';
	DBGPRINTF("ADDR-CMD: (%ld) \'%s\'\n", ptr-m_buf, m_buf);
	m_rdaddr = 0;

	return ptr;
}

char	*TTYBUS::readcmd(const int inc, const int len, char *buf) {
	char	*ptr = buf;

	DBGPRINTF("READCMD: LEN = %d: ", len);
	assert(len < 520);
	assert(len > 0);

	if (len <= 8) {
		*ptr++ = charenc(0x20 + (((len-1)&0x07)<<1) + (inc?1:0));
		DBGPRINTF("%c\n", ptr[-1]);
	} else {
		*ptr++ = charenc(0x30 + (((len-9)>>5)&0x0e) + (inc?1:0));
		*ptr++ = charenc( (len-9) & 0x03f);
		DBGPRINTF("%c%c\n", ptr[-2], ptr[-1]);
	}

	return ptr;
}


/*
 * readv
 *
 * This is the main worker routine for read calls.  readio, readz, readi, all
 * end up here.  readv() reads a buffer of data from the given address, and
 * optionally increments (or not) the address after every read.
 *
 * Parameters:
 *	a	The address to start reading from
 *	inc	'1' if we want to increment the address following each read,
 *		'0' otherwise
 *	len	The number of words to read
 *	buf	A memory buffer storage location to place the results into
 * 
 */
void	TTYBUS::readv(const TTYBUS::BUSW a, const int inc, const int len, TTYBUS::BUSW *buf) {
	const	int	READAHEAD = MAXRDLEN/2, READBLOCK=(MAXRDLEN/2>512)?512:MAXRDLEN/2;
	int	cmdrd = 0, nread = 0;
	// TTYBUS::BUSW	addr = a;
	char	*ptr = m_buf;

	if (len <= 0)
		return;
	DBGPRINTF("READV(%08x,%d,#%4d)\n", a, inc, len);

	ptr = encode_address(a);
	try {
	    while(cmdrd < len) {
		// ptr = m_buf;
		do {
			int	nrd = len-cmdrd;
			if (nrd > READBLOCK)
				nrd = READBLOCK;
			if (cmdrd-nread + nrd>READAHEAD+READBLOCK)
				nrd = READAHEAD+READBLOCK-(cmdrd-nread);
			ptr = readcmd(inc, nrd, ptr);
			cmdrd += nrd;
		} while((cmdrd-nread < READAHEAD+READBLOCK)&&(cmdrd< len));

		*ptr++ = '\n'; *ptr = '\0';
		m_dev->write(m_buf, (ptr-m_buf));

		// DBGPRINTF("Reading %d words\n", (cmdrd-nread));
		while(nread<(cmdrd-READAHEAD)) {
			buf[nread++] = readword();
		} ptr = m_buf;
	    } // DBGPRINTF("Reading %d words, to end the read\n", len-nread);
	    while(nread<len) {
		buf[nread++] = readword();
	    }
	} catch(BUSERR b) {
		DBGPRINTF("READV::BUSERR trying to read %08x\n", a+((inc)?nread:0));
		throw BUSERR(a+((inc)?(nread<<2):0));
	}

	if ((unsigned)m_lastaddr != (a+((inc)?(len<<2):0))) {
		DBGPRINTF("TTYBUS::READV(a=%08x,inc=%d,len=%4x,x) ERR: (Last) %08x != %08x + %08x (Expected)\n", a, inc, len<<2, m_lastaddr, a, (inc)?(len<<2):0);
		printf("TTYBUS::READV(a=%08x,inc=%d,len=%4x,x) ERR: (Last) %08x != %08x + %08x (Expected)\n", a, inc, len<<2, m_lastaddr, a, (inc)?(len<<2):0);
		sleep(1);
		assert((int)m_lastaddr == (a+(inc)?(len<<2):0));
		exit(-3);
	}

	DBGPRINTF("READV::COMPLETE\n");
}

/*
 * readi
 *
 * Read a series of values from bus addresses starting at address a,
 * incrementing the address to read from subsequent addresses along the way.
 *
 * Works by just calling readv to do the heavy lifting.
 */

void	TTYBUS::readi(const TTYBUS::BUSW a, const int len, TTYBUS::BUSW *buf) {
	readv(a, 1, len, buf);
}

/*
 * readi
 *
 * Read a series of values from the bus, with all the values coming from the
 * same address: a.  The address is not incremented between individual word
 * reads.
 *
 * Also calls readv to do the heavy lifting.
 */
void	TTYBUS::readz(const TTYBUS::BUSW a, const int len, TTYBUS::BUSW *buf) {
	readv(a, 0, len, buf);
}

/*
 * readword()
 *
 * Once the read command has been issued, readword() is called to read each
 * word's response from the bus.  This also processes any out of bounds
 * characters, such as interrupt notifications or bus error condition
 * notifications.
 */
TTYBUS::BUSW	TTYBUS::readword(void) {
	TTYBUS::BUSW	val = 0;
	int		nr;
	unsigned	sixbits;

	DBGPRINTF("READ-WORD()\n");

	bool	found_start = false;
	do {
		// Blocking read (for now)
		do {
			nr = lclreadcode(&m_buf[0], 1);
		} while (nr < 1);
		DBGPRINTF("READWORD: -- lclreadcode, nr = %d, m_buf[0] = %c\n", nr, m_buf[0]);

		sixbits = chardec(m_buf[0]);

		if (sixbits&(~0x03f)) {
			// Ignore new lines, unprintables, and characters
			// not a part of our code
			;
		} else if (sixbits < 6) {
			switch(sixbits) {
			case 0:	break; // Idle -- ignore
			case 1: break; // Idle, but the bus is busy
			case 2: break; // Write acknowledgement, ignore it here
			case 3:
				m_bus_err = true;
				DBGPRINTF("READWORD::BUSRESET (unknown addr)\n");
				throw BUSERR(0);
				break;
			case 4:
				m_interrupt_flag = true;
				break;
			case 5:
				DBGPRINTF("READWORD::BUSERR (unknown addr)\n");
				m_bus_err = true;
				throw BUSERR(0);
				break;
			}
		} else if (0x08 == (sixbits & 0x3c)) { // Set 32-bit address
			do {
				nr += lclreadcode(&m_buf[nr], 6-nr);
			} while (nr < 6);

			val = chardec(m_buf[0]) & 0x03;
			val = (val<<6) | (chardec(m_buf[1]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[3]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[4]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[5]) & 0x03f);

			m_addr_set = true;
			m_lastaddr = val<<2;

			DBGPRINTF("RCVD ADDR: 0x%08x\n", val<<2);
		} else if (0x0c == (sixbits & 0x03c)) { // Set 32-bit address,compressed
			int nw = (sixbits & 0x03) + 2;
			do {
				nr += lclreadcode(&m_buf[nr], nw-nr);
			} while (nr < nw);

			if (nw == 2) {
				val = chardec(m_buf[1]);
			} else if (nw == 3) {
				val = chardec(m_buf[1]);
				val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
			} else if (nw == 4) {
				val = chardec(m_buf[1]);
				val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
				val = (val<<6) | (chardec(m_buf[3]) & 0x03f);
			} else { // if (nw == 5)
				val = chardec(m_buf[1]);
				val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
				val = (val<<6) | (chardec(m_buf[3]) & 0x03f);
				val = (val<<6) | (chardec(m_buf[4]) & 0x03f);
			}

			m_addr_set = true;
			m_lastaddr = val<<2;
			DBGPRINTF("RCVD ADDR: 0x%08x (%d bytes)\n", val<<2, nw+1);
		} else
			found_start = true;
	} while(!found_start);

	int	rdaddr;

	DBGPRINTF("READ-WORD() -- sixbits = %02x\n", sixbits);
	if (0x06 == (sixbits & 0x03e)) { // Tbl read, last value
		rdaddr = (m_rdaddr-1)&0x03ff;
		val = m_readtbl[rdaddr];
		m_lastaddr += (sixbits&1)?4:0;
		DBGPRINTF("READ-WORD() -- repeat last value, %08x, A= %08x\n", val, m_lastaddr);
	} else if (0x10 == (sixbits & 0x030)) { // Tbl read, up to 521 into past
		int	idx;
		do {
			nr += lclreadcode(&m_buf[nr], 2-nr);
		} while (nr < 2);

		idx = (chardec(m_buf[0])>>1) & 0x07;
		idx = ((idx<<6) | (chardec(m_buf[1]) & 0x03f)) + 2 + 8;
		rdaddr = (m_rdaddr-idx)&0x03ff;
		val = m_readtbl[rdaddr];
		m_lastaddr += (sixbits&1)?4:0;
		DBGPRINTF("READ-WORD() -- long table value[%3d], %08x, A=%08x\n", idx, val, m_lastaddr);
	} else if (0x20 == (sixbits & 0x030)) { // Tbl read, 2-9 into past
		int	idx;
		idx = (((sixbits>>1)&0x07)+2);
		rdaddr = (m_rdaddr - idx) & 0x03ff;
		val = m_readtbl[rdaddr];
		m_lastaddr += (sixbits&1)?4:0;
		DBGPRINTF("READ-WORD() -- short table value[%3d], %08x, A=%08x\n", idx, val, m_lastaddr);
	} else if (0x38 == (sixbits & 0x038)) { // Raw read
		// DBGPRINTF("READ-WORD() -- RAW-READ, nr = %d\n", nr);
		do {
			nr += lclreadcode(&m_buf[nr], 6-nr);
		} while (nr < 6);

		val = (chardec(m_buf[0])>>1) & 0x03;
		val = (val<<6) | (chardec(m_buf[1]) & 0x03f);
		val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
		val = (val<<6) | (chardec(m_buf[3]) & 0x03f);
		val = (val<<6) | (chardec(m_buf[4]) & 0x03f);
		val = (val<<6) | (chardec(m_buf[5]) & 0x03f);

		m_readtbl[m_rdaddr++] = val; m_rdaddr &= 0x03ff;
		m_lastaddr += (sixbits&1)?4:0;
		DBGPRINTF("READ-WORD() -- RAW-READ %02x:%02x:%02x:%02x:%02x:%02x -- %08x, A=%08x\n",
			m_buf[0], m_buf[1], m_buf[2], m_buf[3],
			m_buf[4], m_buf[5], val, m_lastaddr);
	} else 
		DBGPRINTF("READ-WORD() -- Unknown character, %02x\n", sixbits);

	return val;
}

/*
 * readidle()
 *
 * Reads until the bus becomes idle.  This is called by writev to make sure
 * any write acknowledgements are sufficiently flushed from the stream.  In
 * case anything else is in the stream ... we mostly ignore that here too.
 */
void	TTYBUS::readidle(void) {
	TTYBUS::BUSW	val = 0;
	int		nr = 0;
	unsigned	sixbits;
	bool		found_start = false;

	DBGPRINTF("READ-IDLE()\n");

	while((!found_start)&&(m_dev->available())
			&&((nr=lclreadcode(&m_buf[0], 1))>0)) {
		nr = lclreadcode(&m_buf[0], 1);
		sixbits = chardec(m_buf[0]);

		if (sixbits&(~0x03f)) {
			// Ignore new lines, unprintables, and characters
			// not a part of our code
			;
		} else if (sixbits < 6) {
			switch(sixbits) {
			case 0:	break; // Idle -- ignore
			case 1: break; // Idle, but the bus is busy
			case 2:
				// Write acknowledgement, ignore it here
				// This is one of the big reasons why we are
				// doing this.
				break;
			case 3:
				m_bus_err = true;
				DBGPRINTF("READ-IDLE() - BUSERR\n");
				throw BUSERR(0);
				break;
			case 4:
				m_interrupt_flag = true;
				break;
			case 5:
				m_bus_err = true;
				DBGPRINTF("READ-IDLE() - BUS RESET\n");
				throw BUSERR(0);
				break;
			}
		} else if (0x08 == (sixbits & 0x3c)) { // Set 32-bit address
			do {
				nr += lclreadcode(&m_buf[nr], 6-nr);
			} while (nr < 6);

			val = chardec(m_buf[0]) & 0x03;
			val = (val<<6) | (chardec(m_buf[1]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[3]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[4]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[5]) & 0x03f);

			/* Ignore the address, as we are in readidle();
			m_addr_set = true;
			m_lastaddr = val;
			*/

			DBGPRINTF("RCVD IDLE-ADDR: 0x%08x\n", val);
		} else if (0x0c == (sixbits & 0x03c)) { // Set 32-bit address,compressed
			int nw = (sixbits & 0x03) + 2;
			do {
				nr += lclreadcode(&m_buf[nr], nw-nr);
			} while (nr < nw);

			if (nw == 2) {
				val = chardec(m_buf[1]);
			} else if (nw == 3) {
				val = chardec(m_buf[1]);
				val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
			} else if (nw == 4) {
				val = chardec(m_buf[1]);
				val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
				val = (val<<6) | (chardec(m_buf[3]) & 0x03f);
			} else { // if (nw == 5)
				val = chardec(m_buf[1]);
				val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
				val = (val<<6) | (chardec(m_buf[3]) & 0x03f);
				val = (val<<6) | (chardec(m_buf[4]) & 0x03f);
			}

			/* Ignore address, we are in readidle();
			m_addr_set = true;
			m_lastaddr = val;
			*/
			DBGPRINTF("RCVD IDLE-ADDR: 0x%08x (%d bytes)\n", val, nw+1);
		} else
			found_start = true;
	}

	if (found_start) {
		// We're in readidle().  We don't expect to find any data.
		// But ... we did.  So, just read it off and ignore it.
		int	rdaddr;

		DBGPRINTF("READ-IDLE()  PANIC! -- sixbits = %02x\n", sixbits);
		if (0x06 == (sixbits & 0x03e)) { // Tbl read, last value
			rdaddr = (m_rdaddr-1)&0x03ff;
			val = m_readtbl[rdaddr];
			m_lastaddr += (sixbits&1)?4:0;
			DBGPRINTF("READ-IDLE() -- repeat last value, %08x\n", val);
		} else if (0x10 == (sixbits & 0x030)) { // Tbl read, up to 521 into past
			int	idx;
			do {
				nr += lclreadcode(&m_buf[nr], 2-nr);
			} while (nr < 2);

			idx = (chardec(m_buf[0])>>1) & 0x07;
			idx = ((idx<<6) | (chardec(m_buf[1]) & 0x03f)) + 2 + 8;
			rdaddr = (m_rdaddr-idx)&0x03ff;
			val = m_readtbl[rdaddr];
			m_lastaddr += (sixbits&1)?4:0;
			DBGPRINTF("READ-IDLE() -- long table value[%3d], %08x\n", idx, val);
		} else if (0x20 == (sixbits & 0x030)) { // Tbl read, 2-9 into past
			rdaddr = (m_rdaddr - (((sixbits>>1)&0x07)+2)) & 0x03ff;
			val = m_readtbl[rdaddr];
			m_lastaddr += (sixbits&1)?4:0;
			DBGPRINTF("READ-IDLE() -- short table value[%3d], %08x\n", rdaddr, val);
		} else if (0x38 == (sixbits & 0x038)) { // Raw read
			do {
				nr += lclreadcode(&m_buf[nr], 6-nr);
			} while (nr < 6);
	
			val = (chardec(m_buf[0])>>1) & 0x03;
			val = (val<<6) | (chardec(m_buf[1]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[2]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[3]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[4]) & 0x03f);
			val = (val<<6) | (chardec(m_buf[5]) & 0x03f);

			m_readtbl[m_rdaddr++] = val; m_rdaddr &= 0x03ff;
			m_lastaddr += (sixbits&1)?4:0;
			DBGPRINTF("READ-IDLE() -- RAW-READ %02x:%02x:%02x:%02x:%02x:%02x -- %08x\n",
				m_buf[0], m_buf[1], m_buf[2], m_buf[3],
				m_buf[4], m_buf[5], val);
		} else 
			DBGPRINTF("READ-IDLE() -- Unknown character, %02x\n", sixbits);

	}
}

/*
 * usleep()
 *
 * Called to implement some form of time-limited wait on a response from the
 * bus.
 */
void	TTYBUS::usleep(unsigned ms) {
	if (m_dev->poll(ms)) {
		int	nr;
		nr = m_dev->read(m_buf, 16);
		if (nr == 0) {
			// Connection closed, let it drop
			DBGPRINTF("Connection closed!!\n");
			m_dev->close();
			exit(-1);
		} for(int i=0; i<nr; i++) {
			if (m_buf[i] == TTYC_INT) {
				m_interrupt_flag = true;
				DBGPRINTF("!!!!!!!!!!!!!!!!! ----- INTERRUPT!\n");
			} else if (m_buf[i] == TTYC_IDLE) {
				DBGPRINTF("Interface is now idle\n");
			} else if (m_buf[i] == TTYC_WRITE) {
			} else if (m_buf[i] == TTYC_RESET) {
				DBGPRINTF("Bus was RESET!\n");
			} else if (m_buf[i] == TTYC_ERR) {
				DBGPRINTF("Bus error\n");
			} else if (m_buf[i] == TTYC_BUSY) {
				DBGPRINTF("Interface is ... busy ??\n");
			}
			// else if (m_buf[nr] == 'Q')
			// else if (m_buf[nr] == 'W')
			// else if (m_buf[nr] == '\n')
		}
	}
}

/*
 * wait()
 *
 * Wait for an interrupt condition.
 */
void	TTYBUS::wait(void) {
	if (m_interrupt_flag)
		DBGPRINTF("INTERRUPTED PRIOR TO WAIT()\n");
	do {
		usleep(200);
	} while(!m_interrupt_flag);
}

// TTYBUS:  3503421 ~= 3.3 MB, stopwatch = 1:18.5 seconds, vs 53.8 secs
//	If you issue two 512 word reads at once, time drops to 41.6 secs.
// PORTBUS: 6408320 ~= 6.1 MB, ... 26% improvement, 53 seconds real time

