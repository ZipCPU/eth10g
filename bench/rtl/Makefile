################################################################################
##
## Filename:	bench/rtl/Makefile
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
## Copyright (C) 2023-2025, Gisselquist Technology, LLC
## {{{
## This file is part of the ETH10G project.
##
## The ETH10G project contains free software and gateware, licensed under the
## terms of the 3rd version of the GNU General Public License as published by
## the Free Software Foundation.
##
## This project is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
RTL := ../../rtl
NET := ../../rtl/net

RTLIP := $(NET)/axinwidth.v $(NET)/netfifo.v $(NET)/axincdc.v $(RTL)/afifo.v $(NET)/crc_axin.v $(NET)/crc_eqn.v $(NET)/dropshort.v
TBIP := top.v scoreboard.v crc_calculator.v packet_generator.v tbenet.v

top.vvp: $(TBIP) $(RTLIP)
	iverilog -g2012 -o top.vvp $(TBIP) $(RTLIP) -s top

test: top.vvp

tb_arpcrc.vvp: tb_arpcrc.v $(RTLIP)
	iverilog -g2012 -o tb_arpcrc.vvp tb_arpcrc.v $(RTLIP) -s tb_arpcrc

testcrc: tb_arpcrc.vvp
	vvp tb_arpcrc.vvp
