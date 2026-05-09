#!/usr/bin/perl
################################################################################
##
## Filename:	genreport.pl
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	To direct the formal verification of particular components of
##		the 10Gb Ethernet switch.
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

## Variable declarations
## {{{
$dir = ".";
@proofs = (
	"axinarbiter",
	"axinbroadcast",
	"axinwidth",
	"cecbridge",
	"crc_axin",
	"crc_eqn",
	"dropshort",
	"netfifo",
	"netskid",
	"p642pkt",
	"p66brxgears",
	"p66btxgears",
	"pkt2p64b",
	"pktgate",
	"pktvfiford",
	"pktvfifowr",
	"routetbl",
	"sdckgen",
	"sdcmd",
	"sdrxframe",
	"sdtxframe",
	"sdwb",
	# "sync2stream",
	"txgetports",
	"wbi2cdma",
	"wbmarbiter"
	);

%desc = (
	"axinarbiter"   => "Packet stream N:1 arbiter",
	"axinbroadcast" => "Packet 1:N broadcaster",
	"axinwidth"     => "Packet width adjuster",
	"cecbridge"     => "HDMI CEC Bridge",
	"crc_axin"      => "CRC checker",
	"crc_eqn"       => "CRC Equation generator",
	"dropshort"     => "Abort short packets",
	"netfifo"       => "AXI Network packet FIFO",
	"netskid"       => "AXI Network packet Skid-Buffer",
	"p642pkt"       => "Convert 66b protocol to AXI Network stream",
	"p66brxgears"   => "31/66b Gearbox",
	"p66btxgears"   => "66/64b Gearbox",
	"pkt2p64b"      => "Convert AXI Network stream to p66b protocol",
	"pktgate"       => "Attempts to guarantee complete packets",
	"pktvfiford"    => "Virtual Packet FIFO (Read)",
	"pktvfifowr"    => "Virtual Packet FIFO (Write)",
	"routetbl"      => "Routing table algorithm",
	"sdckgen"       => "SDIO divided clock generator",
	"sdcmd"         => "SDIO command wire processor",
	"sdtxframe"     => "SDIO data transmit generator",
	"sdrxframe"     => "SDIO data receive processor",
	"sdwb"          => "SDIO wishbone command handler",
	# "sync2stream"   => "VGA to AXI video stream converter",
	"txgetports"    => "AXI network packet routing table lookup",
	"wbi2cdma"      => "Low throughput I2C DMA",
	"wbmarbiter"    => "Wishbone N:1 arbiter"
	);
## }}}

## getstatus subroutine
## {{{
# This subroutine runs make, to see if a proof is up to date, or otherwise
# checks the logfile to see what the status was the last time the proof was
# run.
sub getstatus($) {
	my $based = shift;
	my $log = "$based/logfile.txt";

	my $bmc = 0;
	my $ind = 0;
	my $cvr = 0;
	my $ncvr = 0;

	my $PASS = 0;
	my $FAIL = 0;
	my $UNK = 0;
	my $ERR = 0;
	my $terminated = 0;
	my $current = 1;
	my $basepass = 0;

	# print "<TR><TD>Checking make $based/PASS</TD></TR>\n";

	if (open(MAK, "make -n $based/PASS |")) {
		while($line = <MAK>) {
			if ($line =~ /sby/) {
				$current = 0;
			}
		} close(MAK);
	}

	# print "<TR><TD>Opening log, $log</TD></TR>\n";

	open (LOG, "< $log") or return "No log";
	while($line = <LOG>) {
		# print "<TR><TD>LINE=$line</TD></TR>\n";
		if ($line =~ /DONE.*FAIL/) {
			$FAIL = 1;
			# print "<TR><TD>FAIL match</TD></TR>\n";
		} if ($line =~ /basecase.*Status: passed/) {
			$basepass = 1;
			# print "<TR><TD>PASS match</TD></TR>\n";
		} if ($line =~ /DONE.*PASS/) {
			$PASS = 1;
			# print "<TR><TD>PASS match</TD></TR>\n";
		} if ($line =~ /DONE.*UNKNOWN/) {
			$UNK = 1;
			# print "<TR><TD>UNKNOWN match</TD></TR>\n";
		} if ($line =~ /DONE.*ERROR/) {
			$ERR = 1;
			# print "<TR><TD>ERROR match</TD></TR>\n";
		} if ($line =~ /terminating process/) {
			if ($basepass != 0 && $line =~ /basecase: terminating process/) {
			} else {
				$terminated = 1;
			}
		} if ($line =~ /Checking cover/) {
			$cvr = 1;
		} if ($line =~ /engine_\d.induction/) {
			$ind = 1;
			# print "<TR><TD>induction match</TD></TR>\n";
		} if ($line =~ /engine_\d.basecase.*Checking assertions in step\s+(\d+)/) {
			if ($1 > $bmc) {
				$bmc = $1;
				# print "<TR><TD>basecase $bmc match</TD></TR>\n";
			}
		} if ($line =~ /engine_\d:.*Reached cover statement/) {
			$ncvr = $ncvr+1;
		}
	}
	close(LOG);

	if ($PASS) {
		if ($current == 0) {
			"Out of date";
		} elsif ($cvr) {
			"Cover $ncvr";
		} else {
			"PASS";
		}
	} elsif ($FAIL) {
		"FAIL";
	} elsif ($ERR) {
		"ERROR";
	} elsif (($ind == 0 || $UNK != 0) && $bmc > 0) {
		"BMC $bmc";
	} elsif ($terminated) {
		"Terminated";
	} else {
		"Unknown";
	}
}
## }}}

## getelapsed subroutine
## {{{
# This subroutine runs make, to see if a proof is up to date, or otherwise
# checks the logfile to see what the status was the last time the proof was
# run.
sub getelapsed($) {
	my $based = shift;
	my $log = "$based/logfile.txt";
	my $elapsed = "";
	my $tmp, $hrs, $rest, $elhrs=0;

	open (LOG, "< $log") or return "No log";
	while($line = <LOG>) {
		# print "<TR><TD>LINE=$line</TD></TR>\n";
		if ($line =~ /\s+(\d+):(\d\d:\d\d)\s+waiti/) {
			$hrs = $1; $rest = $2;
			$tmp = $hrs . ":" . $rest;
			if ($hrs > $elhrs or ($hrs == $elhrs and $tmp gt $elapsed)) {
				$elapsed = $tmp;
				$elhrs = $hrs;
			}
		} elsif ($line =~ /\s+(\d+):(\d\d:\d\d)\s+Check/) {
			$hrs = $1; $rest = $2;
			$tmp = $hrs . ":" . $rest;
			if ($hrs > $elhrs or ($hrs == $elhrs and $tmp gt $elapsed)) {
				$elapsed = $tmp;
				$elhrs = $hrs;
			}
		} elsif ($line =~ /\s+(\d+):(\d\d:\d\d)\s+Try/) {
			$hrs = $1; $rest = $2;
			$tmp = $hrs . ":" . $rest;
			if ($hrs > $elhrs or ($hrs == $elhrs and $tmp gt $elapsed)) {
				$elapsed = $tmp;
				$elhrs = $hrs;
			}
		}
	}
	close(LOG);

	$elapsed;
}
## }}}

## Start the HTML output
## {{{
## Grab a timestamp
$now = time;
($sc,$mn,$nhr,$ndy,$nmo,$nyr,$nwday,$nyday,$nisdst) = localtime($now);
$nyr = $nyr+1900; $nmo = $nmo+1;
$tstamp = sprintf("%04d%02d%02d",$nyr,$nmo,$ndy);

print <<"EOM";
<HTML><HEAD><TITLE>Formal Verification Report</TITLE></HEAD>
<BODY>
<H1 align=center>10Gb Ethernet Board Verification Report</H1>
<H2 align=center>$tstamp</H2>
<P align=center><TABLE border>
<TR><TH>Status</TH><TH>Elapsed</TH><TH>Component</TD><TH>Proof</TH><TH>Component description</TH></TR>
EOM
## }}}

## Look up all directory entries
## {{{
# We'll use this result to look for subdirectories that might contain
# log files.
opendir(DIR, $dir) or die "Cannot open directory for reading";
my @dirent = readdir(DIR);
closedir(DIR);

# print "@dirent";
## }}}

# Lookup each components proof
foreach $prf (sort @proofs) {
	my $ndirs=0;
	foreach $dent (@dirent) {
		next if (! -d $dent);
		next if ($dent =~ /^\./);
		next if ($dent !~ /^$prf(_\S+)/);
			$subprf = $1;

		$ndirs = $ndirs+1;
	}

	my $firstd = 1;

	# Find each subproof of the component
	foreach $dent (@dirent) {
		## Filter out the wrong directories
		## {{{
		# print("<TR><TD>DIR $dent</TD></TR>\n");
		# Only look at subdirectories
		next if (! -d $dent);
		next if ($dent =~ /^\./);
		next if ($dent !~ /^$prf(_\S+)/);
			$subprf = $1;
		# print("<TR><TD>$dent matches $prf</TD></TR>\n");
		my $st;
		my $el;
		## }}}

		## Get the resulting status
		$st = getstatus($dent);
		$el = getelapsed($dent);
		# print("<TR><TD>STATUS = $st</TD></TR>\n");

		my $link = $prf . $subprf . "/logfile.txt";
		if (-e $link) {
			$link = "<A HREF=\"$link\">";
		} else {
			## print "Not found: $link\n";
			$link = "";
		}

		## Fill out one entry of our table
		## {{{
		my $tail;
		if ($firstd) {
			print "<TR></TR>\n";
			$tail = "</TD><TD>$el</TD><TD>$prf</TD><TD>$subprf</TD><TD rowspan=$ndirs>$desc{$prf}</TD></TR>\n";
			$firstd = 0;
		} else {
			$tail = "</TD><TD>$el</TD><TD>$prf</TD><TD>$subprf</TD></TR>\n";
		} if ($link ne "") {
			$tail = "</A>" . $tail;
		}
		if ($st =~ /PASS/) {
			print "<TR><TD bgcolor=#caeec8>$link" ."Pass$tail";
		} elsif ($st =~ /Cover\s+(\d+)/) {
			my $cvr = $1;
			if ($cvr < 1) {
			print "<TR><TD bgcolor=#ffffca>$link" ."$1 Cover points$tail";
			} else {
			print "<TR><TD bgcolor=#caeec8>$link" ."$1 Cover points$tail";
			}
		} elsif ($st =~ /FAIL/) {
			print "<TR><TD bgcolor=#ffa4a4>$link" ."FAIL$tail";
		} elsif ($st =~ /Terminated/) {
			print "<TR><TD bgcolor=#ffa4a4>$link" ."Terminated$tail";
		} elsif ($st =~ /ERROR/) {
			print "<TR><TD bgcolor=#ffa4a4>$link" ."ERROR$tail";
		} elsif ($st =~ /Out of date/) {
			print "<TR><TD bgcolor=#ffffca>$link" ."Out of date$tail";
		} elsif ($st =~ /BMC\s+(\d+)/) {
			my $bmc = $1;
			if ($bmc < 2) {
			print "<TR><TD bgcolor=#ffa4a4>$link" ."$bmc steps of BMC$tail";
			} else {
			print "<TR><TD bgcolor=#ffffca>$link" ."$bmc steps of BMC$tail";
			}
		} elsif ($st =~ /No log/) {
			print "<TR><TD bgcolor=#e5e5e5>$link" ."No log file found$tail";
		} else {
			print "<TR><TD bgcolor=#e5e5e5>$link" ."Unknown$tail";
		}
		## }}}
	} if ($myfirstd != 0) {
		print "<TR><TD bgcolor=#e5e5e5>Not found</TD><TD>$prf</TD><TD>&nbsp;</TD><TD rowspan=$ndirs>$desc{$prf}</TD></TR>\n";
	}
}

## Finish the HTML log file
## {{{
print <<"EOM";
</TABLE></P>
</BODY></HTML>
EOM
## }}}
