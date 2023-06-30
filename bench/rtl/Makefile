################################################################################
##
## Filename:	Makefile
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	
##
## Creator:	Dan Gisselquist, Ph.D.
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
RTL := ../../rtl
NET := ../../rtl/net

RTLIP := $(NET)/axinwidth.v $(NET)/netfifo.v $(NET)/axincdc.v $(RTL)/afifo.v $(NET)/crc_axin.v
TBIP := top.v scoreboard.v crc_calculator.v packet_generator.v tbenet.v

top.vvp: $(TBIP) $(RTLIP)
	iverilog -g2012 -o top.vvp $(TBIP) $(RTLIP) -s top

test: top.vvp
	vvp top.vvp
