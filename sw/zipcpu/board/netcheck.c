////////////////////////////////////////////////////////////////////////////////
//
// Filename:	netcheck.c
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
#include <stdio.h>
#include <stdlib.h>
#include "board.h"
#include <zipsys.h>

#ifndef	CPUNET_H
int	main(int argc, char **argv) {
	printf("ERR: This design requires both the CPUNET and the ROUTER\n");
}
#else

unsigned calc_crc(int pktlen, const unsigned char *pkt) {
	// {{{
	const unsigned	TAPS = 0xedb88320;
	unsigned	fill = 0xffffffff;

	for(int p=0; p<pktlen; p++) {
		unsigned char	b=pkt[p];

		for(int bit=0; bit<8; bit++) {
			if ((fill ^ b)&1)
				fill = (fill >> 1) ^ TAPS;
			else
				fill >>= 1;

			b >>= 1;
		}
	}

	return fill;
}
// }}}

void	pkt_send(char *pkt, unsigned ln) {
	// {{{
	char	*base  = _cpunet->net_txbase;
	unsigned mlen = _cpunet->net_txlen;
	char	*wptr = (char *)_cpunet->net_txwptr, *endp = base + mlen, *pktp = pkt;
	unsigned	hln;

	// Is there room in the virtual FIFO?
	////************ MISSING CHECK

	// Copy the packet to the virtual FIFO
	// Before any wrap
	hln = ln;
	if (hln + wptr > endp)
		hln = endp - wptr;
	for(int k=0; k<hln; k++)
		*wptr++ = *pktp++;
	if (hln != ln) {
		// After any potential wrap
		hln = ln - hln;
		wptr = base;
		for(int k=0; k<hln; k++)
			*wptr++ = *pktp++;
	}
}
// }}}

unsigned	pkt_recv(char *pkt, unsigned maxln) {
	// {{{
	unsigned	ln;

	if (_cpunet->net_rxwptr == _cpunet->net_rxrptr)
		// FIFO is empty
		return 0;

	ln = *((unsigned *)_cpunet->net_rxrptr);
	if (ln == 0) {
		printf("HW ERR!!  Net length = %d\n", ln);
		_cpunet->net_rxrptr = _cpunet->net_rxwptr;
		return 0;
	} else if (ln > maxln) {
		printf("ERROR !!  JUMBO packet too big at %d bytes\n", ln);
		_cpunet->net_rxrptr = _cpunet->net_rxwptr;
		return 0;
	} else {
		char	*base = _cpunet->net_rxbase;
		unsigned mlen = _cpunet->net_rxlen, hln;
		char	*rptr = (char *)_cpunet->net_rxrptr,
			*endp = base + mlen,
			*pktp = pkt;

		hln = ln;
		if (hln + rptr > endp)
			hln = endp - rptr;
		for(int k=0; k<hln; k++)
			*pktp++ = *rptr++;
		if (hln != ln) {
			// After any potential wrap
			hln = ln - hln;
			rptr = base;
			for(int k=0; k<hln; k++)
				*pktp++ = *rptr++;
		}

		return ln;
	}
}
// }}}

const unsigned	VFIFOSZ = (1<<20);
int main(int argc, char **argv) {
#ifdef	NETRESET_ACCESS
	(*_netreset) = 31;
	__asm__("NOOP");
	__asm__("NOOP");
	__asm__("NOOP");
	__asm__("NOOP");
	(*_netreset) = 3;
#endif
	char	*vfifo_base[4], *ptr;
	char	*vfifo_rx, *vfifo_tx;
	unsigned	start_jiffies, bus_mask, bus_size;

	// Set up the virtual FIFOs
	// {{{
	// Get the bus size
	_gnet->vfif[0].v_memsize = 0;
	_gnet->vfif[0].v_base = (char *)-1;
	bus_mask = (unsigned)_gnet->vfif[0].v_base;
	bus_mask |= ~(VFIFOSZ-1);
	bus_size = -bus_mask;

	for(int k=0; k<4; k++) {
		ptr = (char *)malloc(VFIFOSZ + bus_size);
		// Round up to the next aligned address
		ptr = (char *)((((unsigned)ptr) + (bus_size-1)) & ~(bus_size-1));
		vfifo_base[k] = ptr;
		// Set this address as our base address
		_gnet->vfif[k].v_base    = ptr;
		_gnet->vfif[k].v_memsize = VFIFOSZ;

		// No other registers to set
	}

	ptr = (char *)malloc(VFIFOSZ + bus_size);
	// Round up to the next aligned address
	ptr = (char *)((((unsigned)ptr) + (bus_size-1)) & ~(bus_size-1));
	vfifo_rx = ptr;

	ptr = (char *)malloc(VFIFOSZ + bus_size);
	// Round up to the next aligned address
	ptr = (char *)((((unsigned)ptr) + (bus_size-1)) & ~(bus_size-1));
	vfifo_tx = ptr;

	_cpunet->net_rxbase = vfifo_rx;
	_cpunet->net_rxlen  = VFIFOSZ;
	_cpunet->net_txbase = vfifo_tx;
	_cpunet->net_txlen  = VFIFOSZ;
	// }}}

	// Set up some addresses to use
	// {{{
	char	my_mac[6], fpga1_mac[6], fpga2_mac[6];
	char	my_ip[4], fpga1_ip[4], fpga2_ip[4];

	{
		unsigned tmp1, tmp2;
		tmp1 = _cpunet->net_mac[0];
		tmp2 = _cpunet->net_mac[1];

		my_mac[0] = (tmp1 >> 24);
		my_mac[1] = (tmp1 >> 16);
		my_mac[2] = (tmp1 >>  8);
		my_mac[3] =  tmp1;

		my_mac[4] = (tmp1 >> 24);
		my_mac[5] = (tmp1 >> 16);
	}

	// fpga1_ip = (192 <<24)|(168 <<16)|(0 << 8)|200;
	// fpga2_ip = (192 <<24)|(168 <<16)|(0 << 8)|201;

	fpga1_ip[0]= 192; fpga1_ip[1]= 168; fpga1_ip[2]= 3; fpga1_ip[3]= 200;
	fpga2_ip[0]= 192; fpga2_ip[1]= 168; fpga2_ip[2]= 3; fpga2_ip[3]= 201;

	my_ip[0] = 192; my_ip[1] = 168; my_ip[2] =   3; my_ip[3] = 210;
	// }}}

	//
	// ssh fpga1@192.168.0.200
	// export LANG=en_US.UTF-8
	// export LANGUAGE=en_US
	// fpga1@% ifconfig enp1s0 192.168.3.200 netmask 255.255.255.0
	//
	// ssh fpga2@192.168.0.201
	// export LANG=en_US.UTF-8
	// export LANGUAGE=en_US
	// fpga1@% ifconfig enp1s0 192.168.3.201 netmask 255.255.255.0
	//

	// const	unsigned	ETH_SIZE = 6 + 6 + 2;
	// const	unsigned	IPHDR_SIZE = 20;
	char	*pkt = malloc(128);
	char	*rxpktb;
	const	unsigned	ONE_US = 100;
	const	unsigned	ONE_MS = ONE_US * 1000;
	const	unsigned	ONE_SECOND = ONE_MS * 1000;
	unsigned	crc;
	const	unsigned	MAX_PKTSZ = 65536;

	// Destination MAC
	for(int k=0; k<6; k++)
		pkt[k] = 0x0ff;
	// Source MAC
	for(int k=0; k<6; k++)
		pkt[6 + k] = my_mac[k];
	// EtherType = 0x0806
	pkt[12] = 0x08;
	pkt[13] = 0x06;
	pkt[14] = 0x00;	// HTYPE = 1 / Ethernet
	pkt[15] = 0x01;
	pkt[16] = 0x08;	// PTYPE = 0x800 -> IPv4
	pkt[17] = 0x00;
	pkt[18] = 0x06;	// HLEN = 6 for ethernet
	pkt[19] = 0x04;	// PLEN = 4 for IPv4
	pkt[20] = 0x00;	// Operation = 1
	pkt[21] = 0x01;
	for(int k=0; k<6; k++)
		pkt[22+k] = my_mac[k];	// Sender's ethernet address
	for(int k=0; k<4; k++)
		pkt[28+k] = my_ip[k];	// Sender's IP address
	for(int k=0; k<6; k++)
		pkt[32+k] = 0xff;	// Target's hardware address (unknown)
	for(int k=0; k<4; k++)
		pkt[38+k] = fpga1_ip[k]; // Target's protocol address (unknown)
	for(int k=0; k<40; k++)
		pkt[42+k] = 0;		// Packet padding
	crc = calc_crc(60, pkt);
	pkt[60] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	pkt[61] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	pkt[62] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	pkt[63] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;

	rxpktb = (void *)malloc(MAX_PKTSZ);

	start_jiffies = ONE_SECOND;
	_zip->z_pic = CLEARPIC;
	_zip->z_pic = EINT(SYSINT_JIFFIES);
	_zip->z_jiffies = ONE_SECOND;

	while(1) {
		unsigned	pktln;

		// Let's create a ARP request packet, and send it to FPGA #1
		pkt_send(pkt, 60);
		// Now let's wait a second and see what comes back ...
		while(0 == _zip->z_pic & SYSINT_JIFFIES) {
			pktln = pkt_recv(rxpktb, MAX_PKTSZ);
			if (pktln > 0) {
				printf("RX PKT (%d bytes):\n", pktln);
				for(int k=0; k<pktln; k++)
					printf("%02x ", rxpktb[k]);
				printf("\n");
			}
		}

		start_jiffies += ONE_SECOND;
		// Clear our interrupt
		_zip->z_pic = SYSINT_JIFFIES;
		_zip->z_jiffies = start_jiffies;

	}
}
#endif	// CPUNET_H
