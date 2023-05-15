////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	scopecls.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	After rebuilding the same code over and over again for every
//		"scope" I tried to interact with, I thought it would be simpler
//	to try to make a more generic interface, that other things could plug
//	into.  This file defines and describes that more generic interface.
//
//	More recent updates have added to this interface those things necessary
//	to create a .VCD file for viewing in GTKWave.
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
#ifndef	SCOPECLS_H
#define	SCOPECLS_H

#include <vector>
#include "devbus.h"


/*
 * TRACEINFO
 * {{{
 * The TRACEINFO class describes a wire (or set of wires) internal to the
 * scope data word.  These wires are assumed to be contiguous, and given by:
 * ((data_word>>m_nshift)&((1<<m_nbits)-1).  That is, there are m_nbits bits
 * to this value, and a shift of m_nshift is required to bring them down to
 * zero.
 *
 * Other key pieces include the human readable name given to the signal, m_name,
 * as well as the VCD name, m_key.
 * }}}
 */
class	TRACEINFO {
public:
	const char	*m_name;
	char		m_key[4];
	unsigned	m_nbits, m_nshift;
};

/*
 * SCOPE
 * {{{
 * This class is designed to be a generic SCOPE class, one which has all of the
 * logic other scopes will require.  Hence, if more than one scope needs this
 * logic, I stuff it in here for all scopes to use.
 * }}}
 */
class	SCOPE {
	DEVBUS		*m_fpga;	// Access to the FPGA
	DEVBUS::BUSW	m_addr;		// The address of the scope control reg
			// Set m_compressed to be true if the scope is a
			// compressed scope, that is if it uses the wbscopc.v
			// core.
	bool		m_compressed,
			// Set m_vector_read if you trust the bus enough to
			// issue vector reads (multiple words at once)
			m_vector_read;
	unsigned	m_scoplen,	// Number of words in the scopes memory
			m_holdoff;	// The bias, or samples since trigger
	unsigned	*m_data;	// Data read from the scope
	unsigned	m_clkfreq_hz;

	// The m_traces variable holds a list of all of the various wire
	// definitions within the scope data word.
	std::vector<TRACEINFO *> m_traces;

public:
	SCOPE(DEVBUS *fpga, unsigned addr,
			bool compressed=false, bool vecread=true)
		: m_fpga(fpga), m_addr(addr),
			m_compressed(compressed), m_vector_read(vecread),
			m_scoplen(0), m_data(NULL) {
		//
		// First thing we want to do upon allocating a scope, is to
		// define the traces for that scope.  Sad thing is ... we can't
		// call it here, since the class inheriting from us isn't
		// defined yet.
		// define_traces();


		// Default clock frequency: 100MHz.
		m_clkfreq_hz = 100000000;
	}

	// Free up any of our allocated memory.
	~SCOPE(void) {
		for(unsigned i=0; i<m_traces.size(); i++)
			delete m_traces[i];
		if (m_data) delete[] m_data;
	}

	// Query the scope: Is it ready?  Has it primed, triggered, and stopped?
	// If so, this routine returns true, false otherwise.
	bool	ready();

	// Read the control word from the scope, and send to the standard output
	// a description of that.
	void	decode_control(void);

	// Read the scope's control word, decode the memory size of the scope,
	// and return that to our caller.
	int	scoplen(void);

	// Set the clock speed that we are referencing
	void	set_clkfreq_hz(unsigned clkfreq_hz) {
		m_clkfreq_hz = clkfreq_hz;
	}

	// Read any previously set clock speed.
	unsigned get_clkfreq_hz(void) { return m_clkfreq_hz; }

	// Read the data from the scope and place it into our m_data array.
	// Nothing more is done with it beyond that.
	virtual	void	rawread(void);

	// Walk through the data, and print out to the standard output, what is
	// in it.  If multiple lines have the same data, print() will avoid
	// printing those lines for the purpose of keeping the output from
	// getting cluttered, but it will print a **** spacer, so you know
	// lines were skipped.
		void	print(void);

	// decode() works together with print() above.  The print() routine
	// calls decode() for every memory word within the scope's buffer.
	// More than that, the print() routine starts each line with the
	// clock number of the item, followed by the 32-bit data word in hex and
	// a colon.  Then it calls decode() to fill in the line with whatever
	// useful information was in the scope's data word.  Then it prints
	// a "\n" and continues.  Hence ... the purpose of the decode()
	// function--and why it needs to be scope specific.
	virtual	void	decode(DEVBUS::BUSW v) const = 0;

	//
	//
	// The following routines are provided to enable the creation and
	// writing of VCD files.
	//
	//

	// Write the timescale line to a VCD file.
	virtual void	write_trace_timescale(FILE *fp);

	// Write the offset from the time within the file, to the time of the
	// trigger, into the file.
	virtual void	write_trace_timezero(FILE *fp, int offset);

	// Write the VCD file's header
	virtual void	write_trace_header(FILE *fp, int offset = 0);

	// Given a value, and the number of bits required to define that value,
	// write a single line to our VCD file.
	//
	// This is an internal call that you are not likely to need to modify.
		void	write_binary_trace(FILE *fp, const int nbits,
				unsigned val, const char *str);

	// Same as write_binary_trace above, but this time we are given the
	// trace definition and the un-decomposed word to decompose first before
	// writing to the file.
	//
	// This is also an internal call that you are not likely to need to
	// modify.
		void	write_binary_trace(FILE *fp, TRACEINFO *info,
				unsigned value);

	// This is the user entry point.  When you know the scope is ready,
	// you may call writevcd to start the VCD generation process.
		void	writevcd(const char *trace_file_name);
	// This is an alternate entry point, useful if you already have a
	// FILE *.  This will write the data to the file, but not close the
	// file.
		void	writevcd(FILE *fp);

	// Calculate the number of points the scope covers.  Nominally, this
	// will be m_scopelen, the length of the scope.  However, if the
	// scope is compressed, this could be greater.
	//
	unsigned	getaddresslen(void);

	// Your program needs to define a define_traces() function, which will
	// then be called before trying to write the VCD file.  This function
	// must call register_trace for each of the traces within your data
	// word.
	virtual	void	define_traces(void);

	// Register_trace() defines the elements of a TRACEINFO structure
	// above.  These are then inserted into the list of TRACEINFO
	// structures, for reference when writing the VCD file.
		void	register_trace(const char *varname,
				unsigned nbits, unsigned shift);

	unsigned operator[](unsigned addr) {
		if ((m_data)&&(m_scoplen > 0))
			return m_data[(addr)&(m_scoplen-1)];
		return 0;
	}
};

#endif	// SCOPECLS_H
