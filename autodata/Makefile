################################################################################
##
## Filename:	autodata/Makefile
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	To direct the build of the autofpga automatically generated
##		files.  The various configuration files are the *.txt files
##	found in this directory.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2023-2026, Gisselquist Technology, LLC
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
.PHONY: all
all:	data
#
# Could also depend upon load, if desired, but not necessary
#
# This is the list of components that will form our project.  Each file
# consists of parts and pieces of our project that autofpga will copy/paste
# into our main project files.
#
CLOCKS  := allclocks.txt siclk.txt sirefclk.txt
BASE    := global.txt wbdown.txt icape.txt
AUX     := version.txt pwrcount.txt rtccount.txt	# buserr.txt
IO      := gpio.txt spio.txt
DBGBUS  := wbuconsole.txt
MEMORY  := bkram.txt ddr3.txt flash.txt swload.txt # bkrom.txt
DISKDR  := sdio.txt emmc.txt sdslave.txt sata.txt # cruviemmc.txt
CPU     := zipmaster.txt
## NETWORK := netled.txt		# No network, just network LED testing
## NETWORK := netduplex.txt		# Pass through test, no routing
NETWORK := netrouter.txt cpunet.txt netstats.txt	# Full router, virtual FIFOs, CPU FIFO
GFX     := # hdmi.txt cec.txt edid.txt
SCOPES  := scopepic.txt routescope.txt i2cscope.txt netscope.txt emmcscope.txt satascope.txt zipscope.txt
# Unused scopes: cpunetscope.txt hdmiclrscope.txt rxedidscope.txt flashscope.txt
#	fanscope.txt cfgscope.txt gatescope.txt sdioscope.txt busscope.txt
LDSCRIPT:= mem_bkram_only.txt mem_sdram_only.txt mem_flash_bkram.txt mem_full.txt # mem_bootrom_bkram.txt
OTHER   := i2ccpu.txt fan.txt sirefclkcounter.txt netclk.txt
DATA := $(CLOCKS) $(BASE) $(AUX) $(IO) $(DBGBUS) $(CPU)		\
	$(MEMORY) $(DISKDR) $(NETWORK) $(GFX)			\
	$(SCOPES) $(LDSCRIPT) $(OTHER)

AUTOFPGA := autofpga
$(AUTOFPGA):

.PHONY: data
data: $(AUTOFPGA) $(DATA)
	$(AUTOFPGA) -I .:$(COMMON) -d -o . $(DATA)

.PHONY: clean
## {{{
clean:
	rm -f toplevel.v main.v regdefs.h regdefs.cpp board.h board.ld
	rm -f rtl.make.inc main_tb.cpp
	rm -f dump.txt
## }}}
