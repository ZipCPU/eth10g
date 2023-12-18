////////////////////////////////////////////////////////////////////////////////
//
// Filename:	port.h
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Defines the communication parameters necessary for communicating
//		both with our actual hardware device, as well as with our Verilator
//	simulation.  The result is that whatever communicates with the other may
//	not know the difference (as desired).
//
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
#ifndef	PORT_H
#define	PORT_H

// There are two ways to connect: via a serial port, and via a TCP socket
// connected to a serial port.  This way, we can connect the device on one
// computer, test it, and when/if it doesn't work we can replace the device
// with the test-bench.  Across the network, no one will know any better that
// anything had changed.
#define	FPGAHOST	"localhost"
#define	FPGAPORT	8845

#define FPGAOPEN(V) V= new FPGA(new NETCOMMS(FPGAHOST, FPGAPORT))

#endif
