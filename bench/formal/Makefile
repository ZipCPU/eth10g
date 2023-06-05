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
TESTS := axinarbiter axinbroadcast axinwidth dropshort wbmarbiter
TESTS += pktvfiford pktvfifowr cecbridge wbi2cdma
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl
RTLNET := ../../rtl/net

## Proofs
## {{{
NARB   := axinarbiter
BCAST  := axinbroadcast
NWIDTH := axinwidth
DSHORT := dropshort
WBMARB := wbmarbiter
PKTVRD := pktvfiford
PKTVWR := pktvfifowr
CEC := cecbridge
I2CDMA := wbi2cdma
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
$(PKTVRD): $(PKTVRD)_prf/PASS $(PKTVRD)_prf512/PASS $(PKTVRD)_cvr/PASS
$(PKTVRD)_prf/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN) $(WB)
	sby -f $(PKTVRD).sby prf
$(PKTVRD)_prf512/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN) $(WB)
	sby -f $(PKTVRD).sby prf512
$(PKTVRD)_cvr/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN)
	sby -f $(PKTVRD).sby cvr
## }}}

.PHONY: $(PKTVWR)
## {{{
$(PKTVWR): $(PKTVWR)_prf/PASS $(PKTVWR)_cvr/PASS
$(PKTVWR): $(PKTVWR)_prf512/PASS # $(PKTVWR)_prf32
$(PKTVWR)_prf/PASS: $(PKTVWR).sby   $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby -f $(PKTVWR).sby prf
$(PKTVWR)_prf512/PASS: $(PKTVWR).sby   $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby -f $(PKTVWR).sby prf512
$(PKTVWR)_cvr/PASS: $(PKTVWR).sby   $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
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


.PHONY: report
report:
	+perl genreport.pl > report.html

.PHONY: clean
## {{{
clean:
	rm -rf $(NARB)_*/    $(BCAST)_*/     $(NWIDTH)_*/
	rm -rf $(DSHORT)*/   $(WBMARB)_*/
## }}}
