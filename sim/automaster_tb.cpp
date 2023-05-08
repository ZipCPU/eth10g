////////////////////////////////////////////////////////////////////////////////
//
// Filename:	automaster_tb.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This file calls and accesses the main.v function via the
//		MAIN_TB class found in main_tb.cpp.  When put together with
//	the other components here, this file will simulate (all of) the
//	host's interaction with the FPGA circuit board.
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
#include <signal.h>
#include <time.h>
#include <ctype.h>
#include <string.h>
#include <stdint.h>

#include "verilated.h"
#include "design.h"

#include "testb.h"
// #include "twoc.h"

#include "port.h"

#include "main_tb.cpp"

void	usage(void) {
	// {{{
	fprintf(stderr, "USAGE: main_tb <options> [zipcpu-elf-file]\n");
	fprintf(stderr,
#ifdef	SDSPI_ACCESS
"\t-c <img-file>\n"
"\t\tSpecifies a memory image which will be used to make the SD-card\n"
"\t\tmore realistic.  Reads from the SD-card will be directed to\n"
"\t\t\"sectors\" within this image.\n\n"
#endif
"\t-l <time>\tLimits simulation time to the given time\n"
"\t-d\tSets the debugging flag\n"
"\t-t <filename>\n"
"\t\tTurns on tracing, sends the trace to <filename>--assumed to\n"
"\t\tbe a vcd file\n"
);
}
// }}}

int	main(int argc, char **argv) {
	// Variable declaration and initialization
	// {{{
#if	defined(VIDEO_ACCESS) || defined(OLED_ACCESS)
	Gtk::Main	main_instance(argc, argv);
#endif
	Verilated::commandArgs(argc, argv);

	const	char *elfload = NULL,
#ifdef	SDSPI_ACCESS
			*sdimage_file = NULL,
#endif
			*profile_file = NULL,
			*trace_file = NULL; // "trace.vcd";
	bool	debug_flag = false, willexit = false, verbose_flag = false;
	FILE	*profile_fp;
	uint64_t	limit_time_ns = 0l, limit_time_ps = 0l;

	MAINTB	*tb = new MAINTB;
	// }}}

	// Process arguments
	// {{{
	for(int argn=1; argn < argc; argn++) {
		if (argv[argn][0] == '-') for(int j=1;
					(j<512)&&(argv[argn][j]);j++) {
			switch(tolower(argv[argn][j])) {
#ifdef	SDSPI_ACCESS
			case 'c': sdimage_file = argv[++argn]; j = 1000; break;
#endif
			case 'd': debug_flag = true;
				if (trace_file == NULL)
					trace_file = "trace.vcd";
				break;
			case 'l':
				limit_time_ns = strtoul(argv[++argn], NULL, 0);
				limit_time_ps = limit_time_ns * 1000;
				j = 1000;
				break;
			case 'f': profile_file = "pfile.bin"; break;
			case 't': trace_file = argv[++argn]; j=1000; break;
			case 'h': usage(); exit(0); break;
			case 'v': verbose_flag = true; break;
			default:
				fprintf(stderr, "ERR: Unexpected flag, -%c\n\n",
					argv[argn][j]);
				usage();
				break;
			}
		} else if (iself(argv[argn])) {
			elfload = argv[argn];
#ifdef	SDSPI_ACCESS
		} else if (0 == access(argv[argn], R_OK)) {
			sdimage_file = argv[argn];
#endif
		} else {
			fprintf(stderr, "ERR: Cannot read %s\n", argv[argn]);
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		}
	}
	// }}}

	// Setup
	// {{{
	if (elfload)
		willexit = true;
	if (debug_flag && verbose_flag) {
		printf("Opening design with\n");
		printf("\tDebug Access port = %d\n", FPGAPORT); // fpga_port);
		printf("\tSerial Console    = %d\n", FPGAPORT+1);
		printf("\tVCD File         = %s\n", trace_file);
		if (elfload)
			printf("\tELF File         = %s\n", elfload);
	} if (trace_file)
		tb->opentrace(trace_file);

	if (profile_file) {
#ifndef	INCLUDE_ZIPCPU
		fprintf(stderr, "ERR: Design has no ZipCPU\n");
		exit(EXIT_FAILURE);
#endif
		profile_fp = fopen(profile_file, "w");
		if (profile_fp == NULL) {
			fprintf(stderr, "ERR: Cannot open profile output "
				"file, %s\n", profile_file);
			exit(EXIT_FAILURE);
		}
	} else
		profile_fp = NULL;
	// }}}

#ifndef	INCLUDE_ZIPCPU
	tb->m_core->cpu_sim_cyc  = 0;
	tb->m_core->cpu_sim_stb  = 0;
	tb->m_core->cpu_sim_we   = 0;
	tb->m_core->cpu_sim_addr = 0;
	tb->m_core->cpu_sim_data = 0;
	// tb->m_core->cpu_sim_sel  = 0;
#endif
	tb->reset();
#ifdef	SDSPI_ACCESS
	tb->setsdcard(sdimage_file);
#endif

	// Load the ZipCPU
	// {{{
	if (elfload) {
#ifndef	INCLUDE_ZIPCPU
		fprintf(stderr, "ERR: Design has no ZipCPU\n");
		exit(EXIT_FAILURE);
#endif
		tb->loadelf(elfload);

		ELFSECTION	**secpp;
		uint32_t	entry;

		elfread(elfload, entry, secpp);
		free(secpp);

		if (verbose_flag)
			printf("Attempting to start ZipCPU from 0x%08x\n", entry);

		// Halt the CPU
		// {{{
		tb->cpu_dbg_write(R_ZIPCTRL, CPU_HALT);
		// }}}

		// Clear all registers
		// {{{
		for(int k=0; k<32; k++)
			tb->cpu_dbg_write(R_ZIPREGS+(k*4), 0x00);
		// }}}

		// Write the IPC register
		// {{{
		for(int k=0; k<32; k++)
			tb->cpu_dbg_write(R_ZIPPC, entry);
		// }}}

		// Clear the cache
		// {{{
		tb->cpu_dbg_write(R_ZIPCTRL, CPU_HALT | CPU_CLRCACHE);
		// }}}

		// Start the CPU
		// {{{
		tb->cpu_dbg_write(R_ZIPCTRL, CPU_GO);
		// }}}
	}
	// }}}

	// Main while(1) loop
	// {{{
#if	defined(VIDEO_ACCESS) || defined(OLED_ACCESS)
	tb->connect_idler();
	Gtk::Main::run(*tb->m_hdmi);
#else
	if (profile_fp) { // Profile the ZipCPU
		// {{{
		unsigned last_instruction_tick = 0;
		while((!willexit)||(!tb->done())) {
			unsigned long	iticks;
			unsigned	buf[2];

			tb->tick_clk();

			if (tb->m_core->cpu_prof_stb) {
				unsigned	now;

				now = tb->m_core->cpu_prof_ticks;
				iticks = now - last_instruction_tick;
				buf[0] = tb->m_core->cpu_prof_addr;
				buf[1] = (unsigned)iticks;
				fwrite(buf, sizeof(unsigned), 2, profile_fp);

				last_instruction_tick = now;
			}
		}
		// }}}
	} else if (willexit) {	// Run until an exit call
		// {{{
		if (limit_time_ps == 0) {
			while(!tb->done())
				tb->tick();
		} else {
			while(!tb->done() && limit_time_ps >= tb->m_time_ps)
				tb->tick();
		}
		// }}}
	} else if (limit_time_ps > 0l) {
		while(limit_time_ps >= tb->m_time_ps)
			tb->tick();
	} else	// Run forever
		// {{{
		while(true)
			tb->tick();
		// }}}
#endif
	// }}}

	tb->close();
	delete tb;

	return	EXIT_SUCCESS;
}
