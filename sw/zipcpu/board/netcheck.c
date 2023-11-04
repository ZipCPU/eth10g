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
#include <string.h>
#include "board.h"
#include <zipcpu.h>
#include <zipsys.h>

#ifndef	CPUNET_ACCESS
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
	char	*wptr = (char *)_cpunet->net_txwptr+4,
			*rptr = (char *)_cpunet->net_txrptr,
			*endp = base + mlen,
			*pktp = pkt;
	unsigned	hln, space;

	if (0 == base || 0 == mlen) {
		printf("ERR: PKT-SEND TX FIFO is not configured\n");
		return;
	}

	if (wptr >= endp)
		wptr = base;

	// Is there room in the virtual FIFO?
	// {{{
	space = mlen - (wptr-rptr);
	if (rptr > wptr)	// WRAP
		space -= mlen;
	if (space < ln + 8)
		return;	// NO ROOM
	// }}}

	// Copy the packet to the virtual FIFO
	// {{{
	// Before any wrap
	hln = ln;
	if (hln + wptr > endp)
		hln = endp - wptr;
	memcpy(wptr, pktp, hln);
	if (hln != ln) {
		// After any potential wrap
		pktp += hln;
		hln = ln - hln;
		wptr = base;
		memcpy(base, pktp, hln);
	}
	// }}}

	// Zero the end pointer
	// {{{
	wptr = (char *)_cpunet->net_txwptr + ln + 7;
	wptr = (char *)(((unsigned)wptr) & ~3);
	*((unsigned *)wptr) = 0;
	// }}}

	// Update the FIFOs write pointer
	// {{{
	// Now go back and fill in the packet length
	wptr = (char *)_cpunet->net_txwptr;
	wptr = (char *)(((unsigned)wptr) & ~3);
	*((unsigned *)wptr) = ln;

	// Now we can update the write pointer
	wptr = (char *)_cpunet->net_txwptr + ln + 7;
	wptr = (char *)(((unsigned)wptr) & ~3);
	_cpunet->net_txwptr = wptr;
	// }}}
}
// }}}

unsigned	pkt_recv(char *pkt, unsigned maxln) {
	// {{{
	char	*base = _cpunet->net_rxbase;
	unsigned mlen = _cpunet->net_rxlen, hln, vln;
	char	*wptr = (char *)_cpunet->net_rxwptr,
		*rptr = (char *)_cpunet->net_rxrptr;
	char	*endp = base + mlen,
		*pktp = pkt;
	unsigned	ln;

	if (0 == base || mlen == 0)
		// FIFO is not configured
		return 0;

	if (wptr == rptr)
		// FIFO is empty
		return 0;

printf("RX PKT!\n");

	ln = *((unsigned *)rptr);
	if (ln == 0) {
		printf("HW ERR!!  Net length = %d\n", ln);
		_cpunet->net_rxrptr = wptr;
		return 0;
	} else if (ln > maxln) {
		printf("ERROR !!  JUMBO packet too big at %d bytes\n", ln);
		_cpunet->net_rxrptr = _cpunet->net_rxwptr;
		return 0;
	}

	// SANITY CHECK: Does this packet fit in the virtual FIFO?
	vln = wptr - rptr;
	if (wptr < rptr)
		vln += mlen;
	if (vln < hln + 4) {
		// Reset the FIFO, drop any would-be packets
		_cpunet->net_rxrptr = _cpunet->net_rxwptr;
		return 0;	// NO ROOM
	}

	// Potential wrap due to the pointer being at the end of memory
	rptr += 4;
	if (rptr >= endp)
		rptr = base;

	// Copy our packet out.  First, the packet between here and the endptr
	hln = ln;
	if (hln + rptr > endp)
		hln = endp - rptr;
	memcpy(pktp, rptr, hln);
	// for(int k=0; k<hln; k++) *pktp++ = *rptr++;

	// Then the packet following any potential wraparound
	if (hln != ln) {
		// After any potential wrap
		pktp += hln;
		hln = ln - hln;
		memcpy(pktp, base, hln);
	}

	// Update the pointer
	rptr += ln + 3;
	rptr = (char *)(((unsigned)rptr) & ~3);
	if (rptr >= endp)
		rptr = base;
	_cpunet->net_rxrptr = rptr;

	// Return the size of the packet we just read
	return ln;
}
// }}}

unsigned	read_volatile(unsigned *a) {
	// {{{
	unsigned volatile *p = (unsigned volatile *)a;
	return *p;
}
// }}}

const unsigned	VFIFOSZ = (1<<20);
int main(int argc, char **argv) {
	// Reset our virtual packet FIFOs
	// {{{
	printf("NETCHECK -- Starting up\n");
#ifdef	NETRESET_ACCESS
	// Can't reset everything--we still need to set the addresses, and
	// holding things in reset prevents them from interacting w/ the bus
	// (*_netreset) = 16 | 3;	// 5'b1_0011
	// __asm__("NOOP");
	// __asm__("NOOP");
	// __asm__("NOOP");
	// __asm__("NOOP");
	(*_netreset) = 0;
#endif
	printf("NETCHECK -- Holding two channels in reset\n");
	// }}}

	char	*vfifo_base[4], *ptr;
	char	*vfifo_rx, *vfifo_tx;
	unsigned	start_jiffies, bus_mask, bus_size;
	unsigned	loopctr = 0;

	// Set up the virtual FIFOs
	// {{{
	printf("NETCHECK -- Setting up Virtual FIFOs\n");
	// Get the bus size
	for(unsigned netif=0; netif<4; netif++)
		_gnet->vfif[netif].v_memsize = 0;	// Shut the FIFO down
	for(unsigned netif=0; netif<4; netif++) {
		volatile unsigned	*base;

		base = (volatile unsigned *)&_gnet->vfif[0].v_base;
		*base = -1;
		bus_mask = *base;

		if (bus_mask != 0)
			break;
	}
	// _gnet->vfif[0].v_base = (char *)-1;	// Set all usable bits
	// bus_mask = (volatile unsigned)_gnet->vfif[0].v_base;	// Read the mask back
	if (bus_mask == 0)
		printf("WARNING: No NETFIFOs present!\n");
	printf("NETCHECK -- Bus mask = %08x\n", bus_mask);
	bus_mask |= ~(VFIFOSZ-1);
	printf("NETCHECK -- Bus mask = %08x\n", bus_mask);
	bus_size = -bus_mask;
	printf("NETCHECK -- Bus size = %08x\n", bus_size);

	// Assign VFIFOSZ bytes of memory to each network interface
	// {{{
	for(int k=0; k<4; k++) {
		volatile unsigned	*base;
		unsigned	vfifo_check;

		base = (volatile unsigned *)&_gnet->vfif[k].v_base;
		*base = -1;
		vfifo_check = *base;

		if (vfifo_check) {
			ptr = (char *)malloc(VFIFOSZ + bus_size);
			// Round up to the next aligned address
			ptr= (char *)((((unsigned)ptr) + (bus_size-1)) & ~(bus_size-1));
			vfifo_base[k] = ptr;
			// Set this address as our base address
			printf("VFIFO[%d] assigned to %08x -> %08x\n",
				k, ptr, ptr+VFIFOSZ-1);
			_gnet->vfif[k].v_base    = ptr;
			_gnet->vfif[k].v_memsize = VFIFOSZ;

			// No other registers to set
		} // else ...
		//	No virtual FIFO at this address, don't allocate
		//	any memory for it
	}
	// }}}

	// Now do it again for the CPU's two FIFOs: one for TX and one for RX
	// {{{
	ptr = (char *)malloc(VFIFOSZ + bus_size);
	// Round up to the next aligned address
	ptr = (char *)((((unsigned)ptr) + (bus_size-1)) & ~(bus_size-1));
	vfifo_rx = ptr;

	ptr = (char *)malloc(VFIFOSZ + bus_size);
	// Round up to the next aligned address
	ptr = (char *)((((unsigned)ptr) + (bus_size-1)) & ~(bus_size-1));
	vfifo_tx = ptr;

	printf("CPU-TX    assigned to %08x -> %08x\n",
			vfifo_tx, vfifo_tx+VFIFOSZ-1);
	printf("CPU-RX    assigned to %08x -> %08x\n",
			vfifo_rx, vfifo_rx+VFIFOSZ-1);
	_cpunet->net_txbase = vfifo_tx;
	_cpunet->net_txlen  = VFIFOSZ;
	_cpunet->net_rxbase = vfifo_rx;
	_cpunet->net_rxlen  = VFIFOSZ;

	printf("%08x\n", read_volatile((unsigned int *)&(_cpunet->net_txbase)));
	printf("%08x\n", read_volatile((unsigned int *)&(_cpunet->net_txlen)));
	printf("%08x\n", read_volatile((unsigned int *)&(_cpunet->net_rxbase)));
	printf("%08x\n", read_volatile((unsigned int *)&(_cpunet->net_rxlen)));

	// [0]:	Turn on promiscuous mode
	// [1]:	Enable the FIFO
	// [2]: Clear any errors that may be pending
	_cpunet->net_control= 7;
	// }}}
	// }}}

	// Set up some network addresses to use
	// {{{
	printf("NETCHECK -- Selecting addresses of interest\n");
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

	// Build an ARP request packet
	// {{{
	printf("NETCHECK -- Building an ARP request\n");
	// const	unsigned	ETH_SIZE    = 6 + 6 + 2;
	// const	unsigned	IPHDR_SIZE  = 20;
	// const	unsigned	UDPHDR_SIZE = 8;
	char	*pkt = malloc(128);
	char	*rxpktb;
	const	unsigned	ONE_US = 100;
	const	unsigned	ONE_MS = ONE_US * 1000;
	const	unsigned	ONE_SECOND = ONE_MS * 1000;
	unsigned	crc;
	const	unsigned	MAX_PKTSZ = 65536;

	// Destination MAC = BROADCAST
	for(int k=0; k<6; k++)
		pkt[k] = 0x0ff;
	// Source MAC
	for(int k=0; k<6; k++)
		pkt[6 + k] = my_mac[k];
	// EtherType = 0x0806
	pkt[12] = 0x08;
	pkt[13] = 0x06;

	// ARP header:
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
		pkt[38+k] = fpga1_ip[k]; // Target's protocol (IP) address
	for(int k=0; k<40; k++)
		pkt[42+k] = 0;		// Packet padding
	crc = calc_crc(60, pkt);
	pkt[60] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	pkt[61] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	pkt[62] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	pkt[63] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	// }}}

	rxpktb = (void *)malloc(MAX_PKTSZ);

	start_jiffies = ONE_SECOND;
	_zip->z_pic = CLEARPIC;
	_zip->z_pic = EINT(SYSINT_JIFFIES);
	_zip->z_jiffies = ONE_SECOND;

	printf("NETCHECK -- Setup *COMPLETE*\n");
	while(1) {
		unsigned	pktln;

		// Let's create a ARP request packet, and send it to FPGA #1
		// pkt_send(pkt, 64);
		// Now let's wait a second and see what comes back ...
		while(0 == (_zip->z_pic & SYSINT_JIFFIES)) {
			unsigned char *epay = (unsigned char *)&rxpktb[14],
					*ipay;
			unsigned	ethtype;

			pktln = pkt_recv(rxpktb, MAX_PKTSZ);
			if (pktln > 0) {
				// {{{
				printf("RX PKT (%d bytes):\n", pktln);
				for(int k=0; k<pktln; k++)
					printf("%02x ", rxpktb[k]);
				printf("\n");
				printf("Dst MAC: %02x:%02x:%02x:%02x:%02x:%02x\n",
					rxpktb[0], rxpktb[1], rxpktb[2],
					rxpktb[3], rxpktb[4], rxpktb[5]);
				printf("Src MAC: %02x:%02x:%02x:%02x:%02x:%02x\n",
					rxpktb[6], rxpktb[ 7], rxpktb[ 8],
					rxpktb[9], rxpktb[10], rxpktb[11]);
				printf("EthType: %02x%02x\n",
					rxpktb[12], rxpktb[13]);
				ethtype = (((unsigned char)rxpktb[12]) << 8)
					| ((unsigned char)rxpktb[13]);

				switch(ethtype) {
				case 0x0806:	// ARP
					printf("ARP\n");
					printf("  Operation: %02x%02x\n",
						rxpktb[20], rxpktb[21]);
					printf("  Source IP: %d.%d.%d.%d\n",
						rxpktb[28], rxpktb[29],
						rxpktb[30], rxpktb[31]);
					break;
				case 0x0800:	// IP
					printf("IP\n");
					printf("  Source IP: %d.%d.%d.%d\n",
						epay[ 8], epay[ 9],
						epay[10], epay[11]);
					printf("  Destin IP: %d.%d.%d.%d\n",
						epay[12], epay[13],
						epay[14], epay[15]);
					printf("  PktLength: %d\n",
						(epay[2] << 8) | epay[3]);
					printf("  SubProto : %d\n",
						epay[8]);
					ipay = epay + ((epay[0] & 0x0f)*4);
					switch(epay[8]) {
					case  0: printf("    IP (?)\n");   break;
					case  1: if(ipay[0] == 0)
						  printf("    ICMP - PING\n");
						else if (ipay[0] == 8)
						  printf("    ICMP - REPLY\n");
						break;
					case  6: printf("    TCP\n");  break;
					case 17:
						printf("    UDP : %5d->%5d"
							", %5d bytes\n",
							(ipay[0] << 8)|ipay[1],
							(ipay[2] << 8)|ipay[3],
							(ipay[4] << 8)|ipay[5]);
						break;
					} break;
				default:
					break;
				}
				printf("--------------------------\n");
				// }}}
			} else {
				unsigned check = _cpunet->net_control;

				if (check & 4) {
					printf("CPUNET BUS ERROR!!\n");
					zip_halt();
				}
			}
		}

		start_jiffies += ONE_SECOND;
		// Clear our interrupt
		_zip->z_pic = SYSINT_JIFFIES;
		_zip->z_jiffies = start_jiffies;
		if (loopctr++ >= 32) {
			printf("NETCHECK -- Loop\n");
			loopctr = 0;
		}
	}
}
#endif	// CPUNET_H
