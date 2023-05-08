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
