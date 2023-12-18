////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipjiffies.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This peripheral is motivated by the Linux use of 'jiffies'.
//	A process, in Linux, can request to be put to sleep until a certain
//	number of 'jiffies' have elapsed.  Using this interface, the CPU can
//	read the number of 'jiffies' from this peripheral (it only has the
//	one location in address space), add the sleep length to it, and
//	write the result back to the peripheral.  The zipjiffies peripheral
//	will record the value written to it only if it is nearer the current
//	counter value than the last current waiting interrupt time.  If no
//	other interrupts are waiting, and this time is in the future, it will
//	be enabled.  (There is currrently no way to disable a jiffie interrupt
//	once set.)  The processor may then place this sleep request into a
//	list among other sleep requests.  Once the timer expires, it would
//	write the next jiffy request to the peripheral and wake up the process
//	whose timer had expired.
//
//	Quite elementary, really.
//
// Interface:
//	This peripheral contains one register: a counter.  Reads from the
//	register return the current value of the counter.  Writes within
//	the (N-1) bit space following the current time set an interrupt.
//	Writes of values that occurred in the last 2^(N-1) ticks will be
//	ignored.  The timer then interrupts when its value equals that time.
//	Multiple writes cause the jiffies timer to select the nearest possible
//	interrupt.  Upon an interrupt, the next interrupt time/value is cleared
//	and will need to be reset if the CPU wants to get notified again.  With
//	only the single interface, there is no way of knowing when the next
//	interrupt is scheduled for, neither is there any way to slow down the
//	interrupt timer in case you don't want it overflowing as often and you
//	wish to wait more jiffies than it supports.  Thus, currently, if you
//	have a timer you wish to wait upon that is more than 2^31 into the
//	future, you would need to set timers along the way, wake up on those
//	timers, and set further timer's until you finally get to your
//	destination.
//
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
// terms of the 3rd version of the GNU General Public License as published by
// the Free Software Foundation.
//
// This project is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module	zipjiffies #(
		parameter	BW = 32
	) (
		// {{{
		input	wire			i_clk, i_reset, i_ce,
		// Wishbone inputs
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[(BW-1):0]	i_wb_data,
		input	wire	[BW/8-1:0]	i_wb_sel,
		// Wishbone outputs
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	wire	[(BW-1):0]	o_wb_data,
		// Interrupt line
		output	reg			o_int
		// }}}
	);

	// Local declarations
	// {{{
	reg	[(BW-1):0]		r_counter;
	//
	reg				int_set,  new_set, int_now;
	reg		[(BW-1):0]	int_when, new_when;
	reg	signed	[(BW-1):0]	till_wb,  till_when;
	// }}}

	// r_counter
	// {{{
	// Our counter logic: The counter is always counting up--it cannot
	// be stopped or altered.  It's really quite simple.  Okay, not quite.
	// We still support the clock enable line.  We do this in order to
	// support debugging, so that if we get everything running inside a
	// debugger, the timer's all slow down so that everything can be stepped
	// together, one clock at a time.
	//
	initial	r_counter = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_counter <= 0;
	else if (i_ce)
		r_counter <= r_counter+1;
	// }}}

	// int_now
	// {{{
	initial	int_now = 0;
	always @(posedge i_clk)
	if (i_reset)
		int_now <= 0;
	else if (i_ce)
		int_now <= ((r_counter + 1) == (int_when));
	else
		int_now <= 1'b0;
	// }}}

	// new_set, new_when
	// {{{
	// Writes to the counter set an interrupt--but only if they are in the
	// future as determined by the signed result of an unsigned subtract.
	//
	// assign	till_when = int_when-r_counter;
	// assign	till_wb   = new_when-r_counter;

	initial	new_set = 1'b0;
	always @(posedge i_clk)
	begin
		// Delay WB commands (writes) by a clock to simplify our logic
		new_set <= (i_wb_stb && i_wb_we);
		// new_when is a don't care when new_set = 0, so don't worry
		// about setting it at all times.
		new_when<= i_wb_data;

		till_wb <= (i_wb_data - r_counter - (i_ce ? 1:0));

		till_when <= (int_when - i_wb_data);

		if (i_reset)
			new_set <= 1'b0;
	end
	// }}}

	// o_int, int_set
	// {{{
	initial	o_int   = 1'b0;
	initial	int_set = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		o_int <= 0;
		int_set <= 0;
		// }}}
	end else begin
		// {{{
		o_int <= 1'b0;
		if ((i_ce)&&(int_set)&&(r_counter == int_when))
			// Interrupts are self-clearing
			o_int <= 1'b1;	// Set the interrupt flag for one clock
		else if ((new_set)&&(till_wb <= 0))
			o_int <= 1'b1;

		if ((new_set)&&(till_wb > 0))
			int_set <= 1'b1;
		else if (int_now)
			int_set <= 1'b0;
		// }}}
	end
	// }}}

	// int_when
	// {{{
	always @(posedge i_clk)
	if ((new_set)&&(till_wb > 0)&&((till_when[BW-1])||(!int_set)))
		int_when <= new_when;
	// }}}

	// o_wb_ack
	// {{{
	// Acknowledge any wishbone accesses -- everything we did took only
	// one clock anyway.
	//
	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= i_wb_stb;
	// }}}

	assign	o_wb_data = r_counter;
	assign	o_wb_stall = 1'b0;

	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_wb_sel };
	// verilator lint_on  UNUSED
	// verilator coverage_on
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our inputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// One basic WB assumtion

	// Anytime the stb is high, the cycle line must also be high
	always @(posedge i_clk)
		assume((!i_wb_stb)||(i_wb_cyc));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our bus outputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// We never stall the bus
	always @(*)
		assert(!o_wb_stall);

	// We always ack every transaction on the following clock
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wb_stb)))
	begin
		assert(o_wb_ack);
	end else
		assert(!o_wb_ack);
	// }}}
	///////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our internal state and our outputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
	begin
		assert(!o_wb_ack);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wb_stb))
			&&($past(i_wb_we)))
		assert(new_when == $past(i_wb_data));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wb_stb))
			&&($past(i_wb_we)))
	begin
		assert(new_set);
	end else
		assert(!new_set);

	//
	//
	//

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		assert(!o_int);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
	begin
		assert(!int_set);
		assert(!new_set);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(new_set))
			&&(!$past(till_wb[BW-1]))
			&&($past(till_wb) > 0))
		assert(int_set);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_ce))
		&&($past(r_counter)==$past(int_when)))
	begin
		assert((o_int)||(!$past(int_set)));
		// assert((!int_set)||($past(new_set)));	// !!!!!
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(new_set))&&(!$past(int_set)))
		assert(!int_set);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!o_int);
	end else if (($past(new_set))&&($past(till_wb) < 0))
		assert(o_int);

	always @(posedge i_clk)
	if ((f_past_valid)&&
			((!$past(new_set))
			||($past(till_wb[BW-1]))
			||($past(till_wb == 0))))
		assert(int_when == $past(int_when));
	// }}}
`endif
// }}}
endmodule
