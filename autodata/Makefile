################################################################################
##
## Filename:	auto-data/Makefile
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
.PHONY: all
all:	data
#
# Could also depend upon load, if desired, but not necessary
#
# This is the list of components that will form our project.  Each file
# consists of parts and pieces of our project that autofpga will copy/paste
# into our main project files.
#
CLOCKS  := allclocks.txt
BASE    := global.txt wbdown.txt icape.txt
AUX     := version.txt			# pwrcount.txt rtccount.txt buserr.txt
IO      := gpio.txt spio.txt
DBGBUS  := wbuconsole.txt		# smibus.txt
MEMORY  := bkram.txt flash.txt		# sdram.txt # bkrom.txt
DISKDR  := sdspi.txt			# sata.txt emmc.txt
CPU     := zipmaster.txt smiconsole.txt		# pic.txt
NETWORK :=				#
GFX     :=	# hdmitx.txt hdmirx.txt edid.txt cec.txt # wboledbw.txt
SCOPES  := smiscope.txt flashscope.txt fanscope.txt cfgscope.txt
LDSCRIPT:= mem_bkram_only.txt mem_flash_bkram.txt # mem_bootrom_bkram.txt mem_sdram_only.txt
OTHER   := i2ccpu.txt fan.txt sirefclk.txt
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
