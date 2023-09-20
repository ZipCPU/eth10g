################################################################################
##
## Filename:	Makefile
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	To direct the formal verification of particular internal
##		components of the switch.
##
## Targets:	The default target, all, tests all of the components within
##		this module.
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
TESTS := axinarbiter axinbroadcast axinwidth dropshort wbi2cdma cecbridge
TESTS += pktvfifowr pktvfiford rxgears txgears p642pkt pkt2p64b crc_eqn
# wbmarbiter
# pktvfiford
TESTS += sdckgen sdcmd sdwb sdtxframe sdrxframe
.PHONY: $(TESTS)
all: $(TESTS)
full: all wbmarbiter pktvfiford
RTL := ../../rtl
RTLNET := ../../rtl/net

## Proofs
## {{{
NARB   := axinarbiter
BCAST  := axinbroadcast
NWIDTH := axinwidth
CRCEQ  := crc_eqn
DSHORT := dropshort
RXGEARS:= p66brxgears
TXGEARS:= p66btxgears
P642PKT:= p642pkt
PKT2P64B:= pkt2p64b
WBMARB := wbmarbiter
PKTVRD := pktvfiford
PKTVWR := pktvfifowr
CEC    := cecbridge
I2CDMA := wbi2cdma
SDCK   := sdckgen
SDCMD  := sdcmd
SDWB   := sdwb
SDTX   := sdtxframe
SDRX   := sdrxframe
## }}}

## Interfaces
## {{{
FAXIN := faxin_master.v faxin_slave.v
WB    := fwb_master.v fwb_slave.v
SKID  := $(RTL)/wb2axip/skidbuffer.v
## }}}

.PHONY: $(NARB)
## {{{
$(NARB): $(NARB)_prf/PASS $(NARB)_prflp/PASS $(NARB)_cvr/PASS
$(NARB)_prf/PASS: $(NARB).sby $(RTLNET)/$(NARB).v $(RTLNET)/pktarbiter.v $(FAXIN)
	sby -f $(NARB).sby prf
$(NARB)_prflp/PASS: $(NARB).sby $(RTLNET)/$(NARB).v $(RTLNET)/pktarbiter.v $(FAXIN)
	sby -f $(NARB).sby prflp
$(NARB)_cvr/PASS: $(NARB).sby $(RTLNET)/$(NARB).v $(RTLNET)/pktarbiter.v $(FAXIN)
	sby -f $(NARB).sby cvr
## }}}

.PHONY: $(BCAST)
## {{{
$(BCAST): $(BCAST)_prf/PASS $(BCAST)_prflp/PASS $(BCAST)_cvr/PASS
$(BCAST)_prf/PASS: $(BCAST).sby   $(RTLNET)/$(BCAST).v $(FAXIN)
	sby -f $(BCAST).sby prf
$(BCAST)_prflp/PASS: $(BCAST).sby $(RTLNET)/$(BCAST).v $(FAXIN)
	sby -f $(BCAST).sby prflp
$(BCAST)_cvr/PASS: $(BCAST).sby   $(RTLNET)/$(BCAST).v $(FAXIN)
	sby -f $(BCAST).sby cvr
## }}}

.PHONY: $(CRCEQ)
## {{{
$(CRCEQ): $(CRCEQ)_prf/PASS
$(CRCEQ)_prf/PASS: $(CRCEQ).sby   $(RTLNET)/$(CRCEQ).v
	sby -f $(CRCEQ).sby prf
## }}}

.PHONY: $(NWIDTH)
## {{{
$(NWIDTH): $(NWIDTH)_prv/PASS $(NWIDTH)_cvr/PASS
$(NWIDTH): $(NWIDTH)_prvx8x32/PASS   $(NWIDTH)_prvx32x64/PASS
$(NWIDTH): $(NWIDTH)_prvx64x128/PASS $(NWIDTH)_prvx128x512/PASS
$(NWIDTH): $(NWIDTH)_prvx32x8/PASS   $(NWIDTH)_prvx64x32/PASS
$(NWIDTH): $(NWIDTH)_prvx128x64/PASS $(NWIDTH)_prvx512x128/PASS
$(NWIDTH)_prv/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby prv
$(NWIDTH)_prvx8x32/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby prvx8x32
$(NWIDTH)_prvx32x64/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby prvx32x64
$(NWIDTH)_prvx64x128/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby prvx64x128
$(NWIDTH)_prvx128x512/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby prvx128x512
#
$(NWIDTH)_prvx32x8/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby prvx32x8
$(NWIDTH)_prvx64x32/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby prvx64x32
$(NWIDTH)_prvx128x64/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby prvx128x64
$(NWIDTH)_prvx512x128/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby prvx512x128
#
$(NWIDTH)_cvr/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby -f $(NWIDTH).sby cvr
## }}}

.PHONY: $(DSHORT)
## {{{
$(DSHORT): $(DSHORT)_prf/PASS $(DSHORT)_prflp/PASS $(DSHORT)_cvr/PASS
$(DSHORT)_prf/PASS: $(DSHORT).sby   $(RTLNET)/$(DSHORT).v $(FAXIN)
	sby -f $(DSHORT).sby prf
$(DSHORT)_prflp/PASS: $(DSHORT).sby $(RTLNET)/$(DSHORT).v $(FAXIN)
	sby -f $(DSHORT).sby prflp
$(DSHORT)_cvr/PASS: $(DSHORT).sby   $(RTLNET)/$(DSHORT).v $(FAXIN)
	sby -f $(DSHORT).sby cvr
## }}}

.PHONY: $(RXGEARS) rxgears
## {{{
rxgears: $(RXGEARS)
$(RXGEARS): $(RXGEARS)_prf/PASS $(RXGEARS)_cvr/PASS
$(RXGEARS)_prf/PASS: $(RXGEARS).sby   $(RTLNET)/$(RXGEARS).v
	sby -f $(RXGEARS).sby prf
$(RXGEARS)_cvr/PASS: $(RXGEARS).sby   $(RTLNET)/$(RXGEARS).v
	sby -f $(RXGEARS).sby cvr
## }}}

.PHONY: $(TXGEARS) txgears
## {{{
txgears: $(TXGEARS)
$(TXGEARS): $(TXGEARS)_prf/PASS $(TXGEARS)_cvr/PASS
$(TXGEARS)_prf/PASS: $(TXGEARS).sby   $(RTLNET)/$(TXGEARS).v
	sby -f $(TXGEARS).sby prf
$(TXGEARS)_cvr/PASS: $(TXGEARS).sby   $(RTLNET)/$(TXGEARS).v
	sby -f $(TXGEARS).sby cvr
## }}}

.PHONY: $(P642PKT)
## {{{
$(P642PKT): $(P642PKT)_prf/PASS # $(P642PKT)_cvr/PASS
$(P642PKT)_prf/PASS: $(P642PKT).sby   $(RTLNET)/$(P642PKT).v
	sby -f $(P642PKT).sby prf
$(P642PKT)_cvr/PASS: $(P642PKT).sby   $(RTLNET)/$(P642PKT).v
	sby -f $(P642PKT).sby cvr
## }}}

.PHONY: $(PKT2P64B)
## {{{
$(PKT2P64B): $(PKT2P64B)_prf/PASS $(PKT2P64B)_cvr/PASS
$(PKT2P64B)_prf/PASS: $(PKT2P64B).sby   $(RTLNET)/$(PKT2P64B).v $(FAXIN)
	sby -f $(PKT2P64B).sby prf
$(PKT2P64B)_cvr/PASS: $(P642PKT).sby   $(RTLNET)/$(PKT2P64B).v $(FAXIN)
	sby -f $(PKT2P64B).sby cvr
## }}}

.PHONY: $(WBMARB)
## {{{
$(WBMARB): $(WBMARB)_prf/PASS $(WBMARB)_cvr/PASS
$(WBMARB)_prf/PASS: $(WBMARB).sby $(RTL)/$(WBMARB).v $(RTL)/sfifo.v $(RTLNET)/pktarbiter.v $(WB)
	sby -f $(WBMARB).sby prf
$(WBMARB)_cvr/PASS: $(WBMARB).sby $(RTL)/$(WBMARB).v $(RTL)/sfifo.v $(RTLNET)/pktarbiter.v $(WB)
	sby -f $(WBMARB).sby cvr
## }}}

.PHONY: $(PKTVRD)
## {{{
$(PKTVRD): $(PKTVRD)_prf/PASS    $(PKTVRD)_cvr/PASS
$(PKTVRD): $(PKTVRD)_prf512/PASS $(PKTVRD)_prf32/PASS
$(PKTVRD)_prf/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN) $(WB)
	sby -f $(PKTVRD).sby prf
$(PKTVRD)_prf32/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN) $(WB)
	sby -f $(PKTVRD).sby prf32
$(PKTVRD)_prf512/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN) $(WB)
	sby -f $(PKTVRD).sby prf512
$(PKTVRD)_cvr/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN)
	sby -f $(PKTVRD).sby cvr
## }}}

.PHONY: $(PKTVWR)
## {{{
$(PKTVWR): $(PKTVWR)_prf/PASS    $(PKTVWR)_cvr/PASS
$(PKTVWR): $(PKTVWR)_prf512/PASS $(PKTVWR)_prf32/PASS
$(PKTVWR)_prf/PASS: $(PKTVWR).sby    $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby -f $(PKTVWR).sby prf
$(PKTVWR)_prf32/PASS: $(PKTVWR).sby  $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby -f $(PKTVWR).sby prf32
$(PKTVWR)_prf512/PASS: $(PKTVWR).sby $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby -f $(PKTVWR).sby prf512
$(PKTVWR)_cvr/PASS: $(PKTVWR).sby    $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby -f $(PKTVWR).sby cvr
## }}}

.PHONY: $(CEC)
## {{{
$(CEC): $(CEC)_prf/PASS
$(CEC)_prf/PASS: $(CEC).sby  $(RTL)/hdmi/cecbridge.v
	sby -f $(CEC).sby prf
## }}}

.PHONY: $(I2CDMA)
## {{{
$(I2CDMA): $(I2CDMA)_prf/PASS $(I2CDMA)_cvr/PASS
$(I2CDMA)_prf/PASS: $(I2CDMA).sby  $(RTL)/wbi2c/$(I2CDMA).v $(WB) $(SKID)
	sby -f $(I2CDMA).sby prf
$(I2CDMA)_cvr/PASS: $(I2CDMA).sby  $(RTL)/wbi2c/$(I2CDMA).v $(WB) $(SKID)
	sby -f $(I2CDMA).sby cvr
## }}}

.PHONY: $(SDCMD)
## {{{
$(SDCMD): $(SDCMD)_prf/PASS $(SDCMD)_prfds/PASS # $(SDCMD)_cvr/PASS
$(SDCMD)_prf/PASS: $(SDCMD).sby  $(RTL)/sdspi/$(SDCMD).v
	sby -f $(SDCMD).sby prf
$(SDCMD)_prfds/PASS: $(SDCMD).sby  $(RTL)/sdspi/$(SDCMD).v
	sby -f $(SDCMD).sby prfds
$(SDCMD)_cvr/PASS: $(SDCMD).sby  $(RTL)/sdspi/$(SDCMD).v
	sby -f $(SDCMD).sby cvr
## }}}

.PHONY: $(SDWB)
## {{{
$(SDWB): $(SDWB)_prf/PASS # $(SDCMD)_cvr/PASS
$(SDWB): $(SDWB)_prfds/PASS $(SDWB)_prfdr/PASS
$(SDWB)_prf/PASS: $(SDWB).sby  $(RTL)/sdspi/$(SDWB).v $(WB) fwb_register.v
	sby -f $(SDWB).sby prf
$(SDWB)_prfds/PASS: $(RTL)/sdspi/$(SDWB).v $(SDWB).sby fwb_slave.v fwb_register.v
	sby -f $(SDWB).sby prfds
$(SDWB)_prfdr/PASS: $(RTL)/sdspi/$(SDWB).v $(SDWB).sby fwb_slave.v fwb_register.v
	sby -f $(SDWB).sby prfdr
$(SDWB)_cvr/PASS: $(SDWB).sby  $(RTL)/sdspi/$(SDWB).v $(WB) fwb_register.v
	sby -f $(SDWB).sby cvr
## }}}

.PHONY: $(SDCK)
## {{{
$(SDCK): $(SDCK)_prf/PASS # $(SDCK)_cvr/PASS
$(SDCK)_prf/PASS: $(SDCK).sby  $(RTL)/sdspi/$(SDCK).v
	sby -f $(SDCK).sby prf
$(SDCK)_cvr/PASS: $(SDCK).sby  $(RTL)/sdspi/$(SDCK).v
	sby -f $(SDCK).sby cvr
## }}}

.PHONY: $(SDTX)
## {{{
$(SDTX): $(SDTX)_prf/PASS $(SDTX)_cvr/PASS
$(SDTX)_prf/PASS: $(SDTX).sby  $(RTL)/sdspi/$(SDTX).v
	sby -f $(SDTX).sby prf
$(SDTX)_cvr/PASS: $(SDTX).sby  $(RTL)/sdspi/$(SDTX).v
	sby -f $(SDTX).sby cvr
## }}}

.PHONY: $(SDRX)
## {{{
$(SDRX): $(SDRX)_prf/PASS $(SDRX)_prfs/PASS $(SDRX)_cvr/PASS
$(SDRX)_prf/PASS: $(SDRX).sby  $(RTL)/sdspi/$(SDRX).v
	sby -f $(SDRX).sby prf
$(SDRX)_prfs/PASS: $(SDRX).sby  $(RTL)/sdspi/$(SDRX).v
	sby -f $(SDRX).sby prfs
$(SDRX)_cvr/PASS: $(SDRX).sby  $(RTL)/sdspi/$(SDRX).v
	sby -f $(SDRX).sby cvr
## }}}

SDRX   := sdrxframe

.PHONY: report
report:
	+perl genreport.pl > report.html

.PHONY: clean
## {{{
clean:
	rm -rf $(NARB)_*/    $(BCAST)_*/     $(NWIDTH)_*/
	rm -rf $(DSHORT)*/   $(WBMARB)_*/
## }}}
