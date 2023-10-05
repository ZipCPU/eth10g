################################################################################
##
## Filename:	eth_packet_generator.py
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	Generates a binary file to use as a test source for the 10Gb
##		ethernet test bench.
##
## Ethernet packet structure:
##
##   +----------------------------+
##   | Header                     |   8 octets
##   +----------------------------+
##   | Source MAC Address         |   6 octets
##   +----------------------------+
##   | Destination MAC Address    |   6 octets
##   +----------------------------+
##   | EtherType                  |   2 octets
##   +----------------------------+
##   | Payload                    |   Variable length
##   +----------------------------+
##   | CRC                        |   4 octets
##   +----------------------------+
##
##   Total packet size:
##		22 octets (MAC addresses and EtherType)
###		+ Payload size
##		+ 4 octets (CRC field)
##
## Creator:	Sukru Uzun
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2023, Gisselquist Technology, LLC
## {{{
## This file is part of the ETH10G project.
##
## The ETH10G project contains free software and gateware, licensed under the
## Apache License, Version 2.0 (the "License").  You may not use this project,
## or this file, except in compliance with the License.  You may obtain a copy
## of the License at
## }}}
##	http://www.apache.org/licenses/LICENSE-2.0
## {{{
## Unless required by applicable law or agreed to in writing, files
## distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
## WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
## License for the specific language governing permissions and limitations
## under the License.
##
################################################################################
##
## }}}
import random
import struct
import zlib
import os

def generate_mac_address():
    # Randomly generate 6 bytes
    mac_bytes = [random.randint(0, 0xFF) for _ in range(6)]

    # Pack the bytes into a 6 octets string and return it
    mac_str = struct.pack('BBBBBB', *mac_bytes)
    return mac_str

def swap32_byte(byte_val):
    value = int.from_bytes(byte_val, 'big')  # Byte değerini 32 bitlik tamsayıya dönüştürme
    swapped_value = ((value & 0xFF) << 24) | ((value & 0xFF00) << 8) | ((value >> 8) & 0xFF00) | ((value >> 24) & 0xFF)
    return swapped_value.to_bytes(4, 'big') 

def pad_to_4_bytes(byte_length):
    remainder = byte_length % 4
    
    if remainder == 0:
        return b''
    else:
        padding = 4 - remainder
        padded_val = bytes([0] * padding)
    
    return padded_val

def generate_ethernet_packet(destination_mac, source_mac, ethertype, payload):
    # preamble = "10101010" * 7  # Ethernet frame preamble
    # sfd = "10101011"  # Start-of-Frame delimiter

    ethertype = struct.pack("!H", ethertype)

    packet = (
        # preamble +
        # sfd +
        destination_mac +
        source_mac +
        ethertype +
        payload
    )

    return packet

def write_idle_to_file(filename):
    pkt_bit = 0  # 1 => Packet, 0 => Idle
    err_bit = 0 # random.randint(0, 1)
    print("---------------------------")
    print("pkt_bit =", pkt_bit)
    print("err_bit =", err_bit)

    idle_time = random.randint(2**8, (2**11)-1) # just for now
    print("idle_time =", idle_time)
    header = ((pkt_bit << 31) | (err_bit << 30) | idle_time)

    # convert header from int to binary
    print("Header =", hex(header))
    header_bin = struct.pack('I', header)

    with open(filename, "ab") as file:
        file.write(header_bin)     # write packet

    file.close()

def write_ethernet_packet_to_file(filename, destination_mac, source_mac, ethertype, payload):
    pkt_bit = 1  # 1 => Packet, 0 => Idle
    err_bit = 0 # random.randint(0, 1)
    print("---------------------------")
    print("pkt_bit =", pkt_bit)
    print("err_bit =", err_bit)

    ethernet_packet = generate_ethernet_packet(destination_mac, source_mac, ethertype, payload)
    packet_length = len(ethernet_packet) + 4 # packet length in terms of byte (+4 is CRC length)
    print("packet_length =", packet_length)
    header = ((pkt_bit << 31) | (err_bit << 30) | packet_length)

    # convert header from int to binary
    print("Header =", hex(header))
    header_bin = struct.pack('I', header)
    
    # CRC calculation
    crc = zlib.crc32(ethernet_packet)
    print("crc =", hex(crc))
    crc_bin = struct.pack('I', crc)

    # check if we need padding
    pad_value = pad_to_4_bytes(packet_length)

    # merge packet
    packet = (
        header_bin +
        ethernet_packet +
        crc_bin +
        pad_value
    )

    # split packet into 32 bit words
    chunks = [packet[i:i+4] for i in range(0, len(packet), 4)]

    i = 0
    with open(filename, "ab") as file:
        for part in chunks:
            i = i + 8
            file.write(part)     # write packet
            a = swap32_byte(part)
            print(i/8,": ",a.hex())

    file.close()

source_mac = generate_mac_address()
destination_mac = generate_mac_address()

ethertype = 0x0800  # IPv4

filename = "ethernet_packet.bin"
# delete file content
with open("ethernet_packet.bin", "wb") as dosya:
    pass

for i in range(0,40):
    write_idle_to_file(filename)
    payload_length = random.randint(16*4, (16*4)+32)   # generate random variable length
    payload = os.urandom(payload_length)    # generate random payload
    write_ethernet_packet_to_file(filename, destination_mac, source_mac, ethertype, payload)
