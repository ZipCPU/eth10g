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
TESTS := axinarbiter axinbroadcast axinwidth cecbridge crc_axin crc_eqn
TESTS += dropshort netfifo p642pkt p66brxgears p66btxgears pkt2p64b pktvfifowr
TESTS += pktvfiford routetbl wbi2cdma netskid txgetports pktgate
# wbmarbiter sync2stream
TESTS += sdckgen sdcmd sdwb sdtxframe sdrxframe
.PHONY: $(TESTS)
all: $(TESTS)
full: all wbmarbiter sync2stream
RTL := ../../rtl
RTLNET := ../../rtl/net
SBYFLAGS := -j2 -f

## Proofs
## {{{
NARB   := axinarbiter
BCAST  := axinbroadcast
NWIDTH := axinwidth
CRCEQ  := crc_eqn
DSHORT := dropshort
NFIFO  := netfifo
NSKID  := netskid
P642PKT:= p642pkt
PGATE  := pktgate
PKT2P64B:= pkt2p64b
PKTVRD := pktvfiford
PKTVWR := pktvfifowr
RTBL   := routetbl
RXGEARS:= p66brxgears
TXGEARS:= p66btxgears
TXPORTS:= txgetports
WBMARB := wbmarbiter
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
	sby $(SBYFLAGS) $(NARB).sby prf
$(NARB)_prflp/PASS: $(NARB).sby $(RTLNET)/$(NARB).v $(RTLNET)/pktarbiter.v $(FAXIN)
	sby $(SBYFLAGS) $(NARB).sby prflp
$(NARB)_cvr/PASS: $(NARB).sby $(RTLNET)/$(NARB).v $(RTLNET)/pktarbiter.v $(FAXIN)
	sby $(SBYFLAGS) $(NARB).sby cvr
## }}}

.PHONY: $(BCAST)
## {{{
$(BCAST): $(BCAST)_prf/PASS $(BCAST)_prflp/PASS $(BCAST)_cvr/PASS
$(BCAST)_prf/PASS: $(BCAST).sby   $(RTLNET)/$(BCAST).v $(FAXIN)
	sby $(SBYFLAGS) $(BCAST).sby prf
$(BCAST)_prflp/PASS: $(BCAST).sby $(RTLNET)/$(BCAST).v $(FAXIN)
	sby $(SBYFLAGS) $(BCAST).sby prflp
$(BCAST)_cvr/PASS: $(BCAST).sby   $(RTLNET)/$(BCAST).v $(FAXIN)
	sby $(SBYFLAGS) $(BCAST).sby cvr
## }}}

.PHONY: crc_axin
## {{{
crc_axin := crc_axin_prf/PASS crc_axin_cvr/PASS
crc_axin_prf/PASS: crc_axin.sby   $(RTLNET)/crc_axin.v $(FAXIN)
	sby $(SBYFLAGS) crc_axin.sby prf
crc_axin_cvr/PASS: crc_axin.sby   $(RTLNET)/crc_axin.v $(FAXIN)
	sby $(SBYFLAGS) crc_axin.sby cvr
## }}}

.PHONY: $(CRCEQ)
## {{{
$(CRCEQ): $(CRCEQ)_prf/PASS
$(CRCEQ)_prf/PASS: $(CRCEQ).sby   $(RTLNET)/$(CRCEQ).v
	sby $(SBYFLAGS) $(CRCEQ).sby prf
## }}}

.PHONY: $(NWIDTH)
## {{{
$(NWIDTH): $(NWIDTH)_prv/PASS $(NWIDTH)_cvr/PASS
$(NWIDTH): $(NWIDTH)_prvx8x32/PASS   $(NWIDTH)_prvx32x64/PASS
$(NWIDTH): $(NWIDTH)_prvx64x128/PASS $(NWIDTH)_prvx128x512/PASS
$(NWIDTH): $(NWIDTH)_prvx32x8/PASS   $(NWIDTH)_prvx64x32/PASS
$(NWIDTH): $(NWIDTH)_prvx128x64/PASS $(NWIDTH)_prvx512x128/PASS
$(NWIDTH)_prv/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby prv
$(NWIDTH)_prvx8x32/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby prvx8x32
$(NWIDTH)_prvx32x64/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby prvx32x64
$(NWIDTH)_prvx64x128/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby prvx64x128
$(NWIDTH)_prvx128x512/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby prvx128x512
#
$(NWIDTH)_prvx32x8/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby prvx32x8
$(NWIDTH)_prvx64x32/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby prvx64x32
$(NWIDTH)_prvx128x64/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby prvx128x64
$(NWIDTH)_prvx512x128/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby prvx512x128
#
$(NWIDTH)_cvr/PASS: $(NWIDTH).sby $(RTLNET)/$(NWIDTH).v $(FAXIN)
	sby $(SBYFLAGS) $(NWIDTH).sby cvr
## }}}

.PHONY: $(DSHORT)
## {{{
$(DSHORT): $(DSHORT)_prf/PASS $(DSHORT)_prflp/PASS $(DSHORT)_cvr/PASS
$(DSHORT)_prf/PASS: $(DSHORT).sby   $(RTLNET)/$(DSHORT).v $(FAXIN)
	sby $(SBYFLAGS) $(DSHORT).sby prf
$(DSHORT)_prflp/PASS: $(DSHORT).sby $(RTLNET)/$(DSHORT).v $(FAXIN)
	sby $(SBYFLAGS) $(DSHORT).sby prflp
$(DSHORT)_cvr/PASS: $(DSHORT).sby   $(RTLNET)/$(DSHORT).v $(FAXIN)
	sby $(SBYFLAGS) $(DSHORT).sby cvr
## }}}

.PHONY: $(RXGEARS) rxgears
## {{{
rxgears: $(RXGEARS)
$(RXGEARS): $(RXGEARS)_prf/PASS $(RXGEARS)_cvr/PASS
$(RXGEARS)_prf/PASS: $(RXGEARS).sby   $(RTLNET)/$(RXGEARS).v
	sby $(SBYFLAGS) $(RXGEARS).sby prf
$(RXGEARS)_cvr/PASS: $(RXGEARS).sby   $(RTLNET)/$(RXGEARS).v
	sby $(SBYFLAGS) $(RXGEARS).sby cvr
## }}}

.PHONY: $(TXGEARS) txgears
## {{{
txgears: $(TXGEARS)
$(TXGEARS): $(TXGEARS)_prf/PASS $(TXGEARS)_cvr/PASS
$(TXGEARS)_prf/PASS: $(TXGEARS).sby   $(RTLNET)/$(TXGEARS).v
	sby $(SBYFLAGS) $(TXGEARS).sby prf
$(TXGEARS)_cvr/PASS: $(TXGEARS).sby   $(RTLNET)/$(TXGEARS).v
	sby $(SBYFLAGS) $(TXGEARS).sby cvr
## }}}

.PHONY: $(P642PKT)
## {{{
$(P642PKT): $(P642PKT)_prf/PASS # $(P642PKT)_cvr/PASS
$(P642PKT)_prf/PASS: $(P642PKT).sby   $(RTLNET)/$(P642PKT).v $(FAXIN)
	sby $(SBYFLAGS) $(P642PKT).sby prf
$(P642PKT)_cvr/PASS: $(P642PKT).sby   $(RTLNET)/$(P642PKT).v $(FAXIN)
	sby $(SBYFLAGS) $(P642PKT).sby cvr
## }}}

.PHONY: $(PKT2P64B)
## {{{
$(PKT2P64B): $(PKT2P64B)_prf/PASS $(PKT2P64B)_cvr/PASS
$(PKT2P64B)_prf/PASS: $(PKT2P64B).sby   $(RTLNET)/$(PKT2P64B).v $(FAXIN)
	sby $(SBYFLAGS) $(PKT2P64B).sby prf
$(PKT2P64B)_cvr/PASS: $(P642PKT).sby   $(RTLNET)/$(PKT2P64B).v $(FAXIN)
	sby $(SBYFLAGS) $(PKT2P64B).sby cvr
## }}}

.PHONY: $(WBMARB)
## {{{
$(WBMARB): $(WBMARB)_prf/PASS $(WBMARB)_cvr/PASS
$(WBMARB)_prf/PASS: $(WBMARB).sby $(RTL)/$(WBMARB).v $(RTL)/sfifo.v $(RTLNET)/pktarbiter.v $(WB)
	sby $(SBYFLAGS) $(WBMARB).sby prf
$(WBMARB)_cvr/PASS: $(WBMARB).sby $(RTL)/$(WBMARB).v $(RTL)/sfifo.v $(RTLNET)/pktarbiter.v $(WB)
	sby $(SBYFLAGS) $(WBMARB).sby cvr
## }}}

.PHONY: $(RTBL)
## {{{
$(RTBL): $(RTBL)_prf/PASS    $(RTBL)_cvr/PASS
$(RTBL)_prf/PASS: $(RTBL).sby   $(RTLNET)/$(RTBL).v $(RTLNET)/pktarbiter.v
	sby $(SBYFLAGS) $(RTBL).sby prf
$(RTBL)_cvr/PASS: $(RTBL).sby   $(RTLNET)/$(RTBL).v $(RTLNET)/pktarbiter.v
	sby $(SBYFLAGS) $(RTBL).sby cvr
## }}}

.PHONY: $(PKTVRD)
## {{{
$(PKTVRD): $(PKTVRD)_prf/PASS    $(PKTVRD)_cvr/PASS
$(PKTVRD): $(PKTVRD)_prf512/PASS $(PKTVRD)_prf32/PASS
$(PKTVRD)_prf/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN) $(WB)
	MAKEFLAGS= sby $(SBYFLAGS) -j20 $(PKTVRD).sby prf
$(PKTVRD)_prf32/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN) $(WB)
	MAKEFLAGS= sby $(SBYFLAGS) -j20 $(PKTVRD).sby prf32
$(PKTVRD)_prf512/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN) $(WB)
	MAKEFLAGS= sby $(SBYFLAGS) -j20 $(PKTVRD).sby prf512
$(PKTVRD)_cvr/PASS: $(PKTVRD).sby   $(RTLNET)/$(PKTVRD).v $(FAXIN)
	MAKEFLAGS= sby $(SBYFLAGS) -j20 $(PKTVRD).sby cvr
## }}}

.PHONY: $(PKTVWR)
## {{{
$(PKTVWR): $(PKTVWR)_prf/PASS    $(PKTVWR)_cvr/PASS
$(PKTVWR): $(PKTVWR)_prf512/PASS $(PKTVWR)_prf32/PASS
$(PKTVWR)_prf/PASS: $(PKTVWR).sby    $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby $(SBYFLAGS) $(PKTVWR).sby prf
$(PKTVWR)_prf32/PASS: $(PKTVWR).sby  $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby $(SBYFLAGS) $(PKTVWR).sby prf32
$(PKTVWR)_prf512/PASS: $(PKTVWR).sby $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby $(SBYFLAGS) $(PKTVWR).sby prf512
$(PKTVWR)_cvr/PASS: $(PKTVWR).sby    $(RTLNET)/$(PKTVWR).v $(FAXIN) $(WB)
	sby $(SBYFLAGS) $(PKTVWR).sby cvr
## }}}

.PHONY: $(NSKID)
## {{{
$(NSKID): $(NSKID)_prf/PASS
$(NSKID)_prf/PASS: $(NSKID).sby $(RTLNET)/$(NSKID).v $(FAXIN)
	sby $(SBYFLAGS) $(NSKID).sby prf
## }}}

.PHONY: $(NFIFO)
## {{{
$(NFIFO): $(NFIFO)_prf/PASS    $(NFIFO)_prf_wr/PASS
$(NFIFO): $(NFIFO)_prf_w/PASS  $(NFIFO)_prf_r/PASS
$(NFIFO): $(NFIFO)_prf_a/PASS  $(NFIFO)_prf_awr/PASS
$(NFIFO): $(NFIFO)_prf_aw/PASS $(NFIFO)_prf_ar/PASS
$(NFIFO): $(NFIFO)_cvr/PASS
$(NFIFO)_prf/PASS: $(NFIFO).sby $(RTLNET)/$(NFIFO).v $(FAXIN)
	sby $(SBYFLAGS) $(NFIFO).sby prf
$(NFIFO)_prf_r/PASS: $(NFIFO).sby $(RTLNET)/$(NFIFO).v $(FAXIN)
	sby $(SBYFLAGS) $(NFIFO).sby prf_r
$(NFIFO)_prf_w/PASS: $(NFIFO).sby $(RTLNET)/$(NFIFO).v $(FAXIN)
	sby $(SBYFLAGS) $(NFIFO).sby prf_w
$(NFIFO)_prf_wr/PASS: $(NFIFO).sby $(RTLNET)/$(NFIFO).v $(FAXIN)
	sby $(SBYFLAGS) $(NFIFO).sby prf_wr
$(NFIFO)_prf_a/PASS: $(NFIFO).sby $(RTLNET)/$(NFIFO).v $(FAXIN)
	sby $(SBYFLAGS) $(NFIFO).sby prf_a
$(NFIFO)_prf_ar/PASS: $(NFIFO).sby $(RTLNET)/$(NFIFO).v $(FAXIN)
	sby $(SBYFLAGS) $(NFIFO).sby prf_ar
$(NFIFO)_prf_aw/PASS: $(NFIFO).sby $(RTLNET)/$(NFIFO).v $(FAXIN)
	sby $(SBYFLAGS) $(NFIFO).sby prf_aw
$(NFIFO)_prf_awr/PASS: $(NFIFO).sby $(RTLNET)/$(NFIFO).v $(FAXIN)
	sby $(SBYFLAGS) $(NFIFO).sby prf_awr
$(NFIFO)_cvr/PASS: $(NFIFO).sby $(RTLNET)/$(NFIFO).v $(FAXIN)
	sby $(SBYFLAGS) $(NFIFO).sby cvr
## }}}

.PHONY: $(PGATE)
## {{{
$(PGATE): $(PGATE)_prf/PASS    $(PGATE)_prf_wr/PASS
$(PGATE): $(PGATE)_prf_w/PASS  $(PGATE)_prf_r/PASS
$(PGATE): $(PGATE)_prf_a/PASS  $(PGATE)_prf_awr/PASS
$(PGATE): $(PGATE)_prf_aw/PASS $(PGATE)_prf_ar/PASS
$(PGATE): $(PGATE)_cvr/PASS
$(PGATE)_prf/PASS: $(PGATE).sby $(RTLNET)/$(PGATE).v $(FAXIN)
	sby $(SBYFLAGS) $(PGATE).sby prf
$(PGATE)_prf_r/PASS: $(PGATE).sby $(RTLNET)/$(PGATE).v $(FAXIN)
	sby $(SBYFLAGS) $(PGATE).sby prf_r
$(PGATE)_prf_w/PASS: $(PGATE).sby $(RTLNET)/$(PGATE).v $(FAXIN)
	sby $(SBYFLAGS) $(PGATE).sby prf_w
$(PGATE)_prf_wr/PASS: $(PGATE).sby $(RTLNET)/$(PGATE).v $(FAXIN)
	sby $(SBYFLAGS) $(PGATE).sby prf_wr
$(PGATE)_prf_a/PASS: $(PGATE).sby $(RTLNET)/$(PGATE).v $(FAXIN)
	sby $(SBYFLAGS) $(PGATE).sby prf_a
$(PGATE)_prf_ar/PASS: $(PGATE).sby $(RTLNET)/$(PGATE).v $(FAXIN)
	sby $(SBYFLAGS) $(PGATE).sby prf_ar
$(PGATE)_prf_aw/PASS: $(PGATE).sby $(RTLNET)/$(PGATE).v $(FAXIN)
	sby $(SBYFLAGS) $(PGATE).sby prf_aw
$(PGATE)_prf_awr/PASS: $(PGATE).sby $(RTLNET)/$(PGATE).v $(FAXIN)
	sby $(SBYFLAGS) $(PGATE).sby prf_awr
$(PGATE)_cvr/PASS: $(PGATE).sby $(RTLNET)/$(PGATE).v $(FAXIN)
	sby $(SBYFLAGS) $(PGATE).sby cvr
## }}}

.PHONY: $(TXPORTS)
## {{{
$(TXPORTS): $(TXPORTS)_prf/PASS $(TXPORTS)_prflp/PASS  $(TXPORTS)_cvr/PASS
$(TXPORTS)_prf/PASS: $(TXPORTS).sby   $(RTLNET)/$(TXPORTS).v $(FAXIN)
	sby $(SBYFLAGS) $(TXPORTS).sby prf
$(TXPORTS)_prflp/PASS: $(TXPORTS).sby   $(RTLNET)/$(TXPORTS).v $(FAXIN)
	sby $(SBYFLAGS) $(TXPORTS).sby prflp
$(TXPORTS)_cvr/PASS: $(TXPORTS).sby   $(RTLNET)/$(TXPORTS).v $(FAXIN)
	sby $(SBYFLAGS) $(TXPORTS).sby cvr
## }}}

.PHONY: $(CEC)
## {{{
$(CEC): $(CEC)_prf/PASS
$(CEC)_prf/PASS: $(CEC).sby  $(RTL)/hdmi/cecbridge.v
	sby $(SBYFLAGS) $(CEC).sby prf
## }}}

.PHONY: $(I2CDMA)
## {{{
$(I2CDMA): $(I2CDMA)_prf/PASS $(I2CDMA)_cvr/PASS
$(I2CDMA)_prf/PASS: $(I2CDMA).sby  $(RTL)/wbi2c/$(I2CDMA).v $(WB) $(SKID)
	sby $(SBYFLAGS) $(I2CDMA).sby prf
$(I2CDMA)_cvr/PASS: $(I2CDMA).sby  $(RTL)/wbi2c/$(I2CDMA).v $(WB) $(SKID)
	sby $(SBYFLAGS) $(I2CDMA).sby cvr
## }}}

.PHONY: $(SDCMD)
## {{{
$(SDCMD): $(SDCMD)_prf/PASS $(SDCMD)_prfds/PASS # $(SDCMD)_cvr/PASS
$(SDCMD)_prf/PASS: $(SDCMD).sby  $(RTL)/sdspi/$(SDCMD).v
	sby $(SBYFLAGS) $(SDCMD).sby prf
$(SDCMD)_prfds/PASS: $(SDCMD).sby  $(RTL)/sdspi/$(SDCMD).v
	sby $(SBYFLAGS) $(SDCMD).sby prfds
$(SDCMD)_cvr/PASS: $(SDCMD).sby  $(RTL)/sdspi/$(SDCMD).v
	sby $(SBYFLAGS) $(SDCMD).sby cvr
## }}}

.PHONY: $(SDWB)
## {{{
$(SDWB): $(SDWB)_prf/PASS # $(SDCMD)_cvr/PASS
$(SDWB): $(SDWB)_prfds/PASS $(SDWB)_prfdr/PASS
$(SDWB)_prf/PASS: $(SDWB).sby  $(RTL)/sdspi/$(SDWB).v $(WB) fwb_register.v
	sby $(SBYFLAGS) $(SDWB).sby prf
$(SDWB)_prfds/PASS: $(RTL)/sdspi/$(SDWB).v $(SDWB).sby fwb_slave.v fwb_register.v
	sby $(SBYFLAGS) $(SDWB).sby prfds
$(SDWB)_prfdr/PASS: $(RTL)/sdspi/$(SDWB).v $(SDWB).sby fwb_slave.v fwb_register.v
	sby $(SBYFLAGS) $(SDWB).sby prfdr
$(SDWB)_cvr/PASS: $(SDWB).sby  $(RTL)/sdspi/$(SDWB).v $(WB) fwb_register.v
	sby $(SBYFLAGS) $(SDWB).sby cvr
## }}}

.PHONY: $(SDCK)
## {{{
$(SDCK): $(SDCK)_prf/PASS # $(SDCK)_cvr/PASS
$(SDCK)_prf/PASS: $(SDCK).sby  $(RTL)/sdspi/$(SDCK).v
	sby $(SBYFLAGS) $(SDCK).sby prf
$(SDCK)_cvr/PASS: $(SDCK).sby  $(RTL)/sdspi/$(SDCK).v
	sby $(SBYFLAGS) $(SDCK).sby cvr
## }}}

.PHONY: $(SDTX)
## {{{
$(SDTX): $(SDTX)_prf/PASS $(SDTX)_cvr/PASS
$(SDTX)_prf/PASS: $(SDTX).sby  $(RTL)/sdspi/$(SDTX).v
	sby $(SBYFLAGS) $(SDTX).sby prf
$(SDTX)_cvr/PASS: $(SDTX).sby  $(RTL)/sdspi/$(SDTX).v
	sby $(SBYFLAGS) $(SDTX).sby cvr
## }}}

.PHONY: $(SDRX)
## {{{
$(SDRX): $(SDRX)_prf/PASS $(SDRX)_prfs/PASS $(SDRX)_cvr/PASS
$(SDRX)_prf/PASS: $(SDRX).sby  $(RTL)/sdspi/$(SDRX).v
	sby $(SBYFLAGS) $(SDRX).sby prf
$(SDRX)_prfs/PASS: $(SDRX).sby  $(RTL)/sdspi/$(SDRX).v
	sby $(SBYFLAGS) $(SDRX).sby prfs
$(SDRX)_cvr/PASS: $(SDRX).sby  $(RTL)/sdspi/$(SDRX).v
	sby $(SBYFLAGS) $(SDRX).sby cvr
## }}}

SDRX   := sdrxframe

.PHONY: report
report:
	+perl genreport.pl > report.html

.PHONY: clean
## {{{
clean:
	rm -rf $(NARB)_*/    $(BCAST)_*/     $(NWIDTH)_*/
	rm -rf $(CRCEQ)_*/
	rm -rf $(DSHORT)_*/
	rm -rf $(RXGEARS)_*/ $(TXGEARS)_*/
	rm -rf $(P642PKT)_*/ $(PKT2P64B)_*/
	rm -rf $(CEC)_*/     $(I2CDMA)_*/
	rm -rf $(SDCK)_*/    $(SDCMD)_*/
	rm -rf $(SDWB)_*/    $(SDTX)_*/
	rm -rf $(SDRX)_*/    $(RTBL)_*/
	rm -rf $(NSKID)_*/   $(NFIFO)_*/
	rm -rf $(TXPORTS)_*/ $(PGATE)_*/
	rm -rf $(PKTVRD)_*/  $(PKTVWR)_*/
	rm -rf $(WBMARB)_*/  $(PKTVWR)_*/
## }}}
