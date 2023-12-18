# An Open Source 10Gb Ethernet Switch

The main goal of this project is to demonstrate a 10Gb Ethernet switch.
Packets will arrive in one of four SFP+ interfaces, and from there be routed
as appropriately.

## Routing algorithm

The [current (draft) routing algorithm](rtl/net/routecore.v) is as follows:

1. For each incoming packet, its incoming port and source MAC address will be
   [captured](rtl/net/rxgetsrcmac.v), and then [recorded in a table](rtl/net/routetbl.v).

   - The table will have timeouts for all entries.
   - If the [table](rtl/net/routetbl.v) is full, the new entry will overwrite the oldest entry

2. For each outgoing packet, if the destination MAC address matches the
   source address seen on a previous incoming source MAC address, the packet
   will be routed to that port.

3. In all other cases, if the port cannot be determined or if the destination
   port is to a broadcast address, the packet will be broadcast to all (other)
   ports.

4. One address has been [reserved and used for a local soft-core CPU](rtl/net/cpunet.v).

## Other hardware interfaces

Other hardware interfaces are also be present within this design, to include
[UART](https://github.com/ZipCPU/wbuart32), [HDMI Tx and
Rx](https://github.com/ZipCPU/vgasim), a SATA controller (still under
development), [micro SD, eMMC](https://github.com/ZipCPU/sdspi),
[QSPI flash](https://github.com/ZipCPU/qspiflash),
[I2C](https://github.com/ZipCPU/wbi2c), temperature sensing and [fan
control](rtl/wbfan.v), and much more.

- [UART console via the debugbus](rtl/wbubus/wbuconsole.v)
- [uSD and EMMC](rtl/sdspi/sdspi.v)
- [QSPI Flash](rtl/qflexpress.v)
- [I2C](rtl/wbi2c/wbi2ccpu.v)
  - Si5324 clock generator
  - B/W OLED display
- [SPIO: 5 buttons, 8 LEDs, and 9 switches](rtl/spio.v)
- [HDMI RX and TX](rtl/hdmi)
- [RPi CM4 SMI interface](rtl/smi/smi.v)
- SATA
- [Open Source Verilog DDR3 SDRAM controller](https://github.com/AngeloJacobo/DDR3_Controller).

## Sponsorship

[This project was sponsored](https://www.netidee.at/fastopenswitch) by [NetIdee](https://www.netidee.at).

## License

This project is released under the [GPLv3 license](doc/gpl-3.0.pdf).  This
should be sufficient for most individual needs.  Should you find this license
insufficient to meet your needs, other licenses can be purchased from
Gisselquist Technology, LLC.

## Status

As of 30 November, 2023:

- The initial PCB for this project has been built and testing has completed.  Several issues have been found, which are now scheduled to be fixed in the next revision.

- The project RTL is mostly assembled.  The only significant component not yet integrated is the SATA.

- Components assembled, attached, and demonstrated to be working include:

  - The bus RTL has been assembled, to include the [Wishbone crossbar](rtl/wb2axip/rtl/wbxbar.v)s, as well as [up](rtl/wb2axip/wbupsz.v) and [down](rtl/wb2axip/wbdown.v) sizing components.

  - The [debug bus](https://github.com/ZipCPU/dbgbus), [the ZipCPU](https://github.com/ZipCPU/zipcpu), its [console](https://github.com/ZipCPU/wbuart32), and the [ZipCPU's (new) DMA](rtl/cpu/zipdma.v).  All four are running, and are currently an integral part of testing.  This includes STDLIB and STDIO (i.e. printf) support via [NEWLIB](https://sourceware.org/newlib).

  - Several [Wishbone Scopes](https://github.com/ZipCPU/wbscope) have been used to debug things so far.

  - _Was working:_ The [QSPI flash](rtl/qflexpress.v).  (The control wires have since been disconnected on the board, due to a conflict with the SDIO.  This will be fixed in the next PCB revision.)  A voltage conflict kept the board from configuring itself from the flash on power up.  Both of these issues should be fixed in the next board revision.  _This controller has been removed from the currently active design._

  - The [ICAPE port](https://github.com/ZipCPU/wbicapetwo).  Once the flash hardware has been fixed, this peripheral will allow the design to issue warm configuration restart requests.

  - The [I2C Controller](rtl/wbi2c/wbi2ccpu.v), to include a new [I2C DMA](rtl/wbi2c/wbi2cdma.v).

    - [Fan control and temperature measurement](rtl/wbfan.v).  The [I2C controller](rtl/wbi2c/wbi2ccpu.v) is used here to sense temperature, and so it is an integral part of the [fan controller](rtl/wbfan.v).  This is not (yet) a closed loop system, however, since the board is currently using a heat sink instead of a fan.

    - [EDID information](https://en.wikipedia.org/wiki/Extended_Display_Identification_Data) may be successfully read from the downstream HDMI port, and pushed upstream to support the HDMI receiver.

    - DDR3 configuration information may be read successfully from the DDR3 daughter board

    - [SFP+](https://en.wikipedia.org/wiki/Small_Form-factor_Pluggable) configuration information may also be read, and interpreted according to SFF-8472.  This information was used successfully in the early rounds of debugging the Ethernet ports.

    - [Si5324 reference clock controller](https://zipcpu.com/blog/2019/06/28/genclk.html).  The clock can be configured, and also measured within the FPGA.

    - [OLED display](https://www.amazon.com/Teyleten-Robot-Display-SSD1306-Raspberry/dp/B08ZY4YBHL/) via I2C.  You can see a [demonstration image here](doc/ssdlogo-demo.png).

  - [General](rtl/gpio.v) and [Special Purpose IO](rtl/spio.v) controllers.  This means that all [buttons, switches, and LEDs](rtl/spio.v) are working.

  - SD/eMMC:

    - [SPI based SD card controller](https://github.com/ZipCPU/sdspi).  This worked long enough to prove itself.  [The SPI-based controller](rtl/sdspi/sdspi.v) has since been removed from the design in favor of its [companion SDIO based controller](rtl/sdspi/sdio.v).

    - The [SDIO SD card controller](https://github.com/ZipCPU/sdspi) is now working on the board after replacing one of the level shifting chips on the board.

    - The eMMC device, which also uses the [SDIO controller](https://github.com/ZipCPU/sdspi), is working as well.  The [software driver](sw/zipcpu/fatfs/emmcdrvr.c) could use some more work, but the PCB/chip/RTL device appears to be working just fine.

    - Filesystem support is being provided by [FATFS](http://elm-chan.org/fsw/ff/00index_e.html).  It has been used to (successfully) read the directory of an attached SD Card.

  - _(Sort of) Working:_ [SMI Slave Controller](rtl/smi/smi.v).  The SMI pins appear to work--all except the SMI address pins.  I'm not sure why that is, but appears to be a design issue with the [CM4 daughter board](https://www.raspberrypi.com/products/compute-module-4/?variant=raspberry-pi-cm4001000).  Still, it's working well enough that the project can use SMI if desired.

  - [HDMI transmitter/receiver](rtl/hdmi/vidpipe.v).  The receiver now accepts video from the RPi and forwards it downstream.  Either this video, or a blank screen, can then be forwarded to an overlay module.  The result has now been display (successfully) via the HDMI transmitter.  _(This component has since been temporarily removed for a lack of available space in the FPGA.)_

  - The 10Gb Ethernet component.  All connections are up and running in our test setup.  The router itself appears to be working as well.

  - This open source [DDR3 SDRAM memory controller](https://github.com/AngeloJacobo/DDR3_Controller).  While I haven't (yet) measured its performance, I'm expecting this controller to a 2x lower latency when compared with Xilinx's MIG controller.

  - [The CPU-based virtual packet FIFOs](rtl/net/cpunet.v) are fully integrated, and appear to be working.


- Only one component remains to be integrated and tested:

  - [The SATA Controller](https://github.com/ZipCPU/wbsata).  This component needs some more development time at present.


The next steps for this project include:

- Measuring the network throughput.  [iperf](https://iperf.fr/) has been
  recommended for this purpose.

- Completing the [SATA controller](https://github.com/ZipCPU/wbsata).

  This task is not yet funded.

- Updating the simulation so that it can simulate the entire design.

  Currently the design has no functional top level simulation.
  This is due to a lack of simulation models for key subsystems, to include
  the [DDR3 SDRAM](https://github.com/AngeloJacobo/DDR3_Controller) and the
  [EMMC](https://github.com/ZipCPU/sdspi).  Whether these remaining models
  get built in Verilog, C++ for use with Verilator, or both is a decision
  that remains to be made.

  This task is not currently funded, as all of the funded tasks associated
  with this project have been completed.

To track the project's status at a glance, you can check either the [bus blocks
testing stoplight chart](doc/eth10g-busblocks.png), or the [10Gb Ethernet
testing](doc/eth10g-blocks.png) diagram.  Both show the status of the hardware
testing of various components within the system, although from different
viewpoints.  The [bus blocks](doc/eth10g-busblocks.png) chart shows the status
of the various components connected to the backbone Wishbone bus, but doesn't
really break down the 10Gb ethernet components. The [10Gb Ethernet
blocks](doc/eth10g-blocks.png) diagram, on the other hand, breaks down the
status of the 10Gb Ethernet components, but doesn't show the status of the
rest of the design.  Together, both will provide insight into the current
state of the design.

Ideally, the [dev branch of this
project](https://github.com/ZipCPU/eth10g/tree/dev) would have the most recent
status.  In practice, the [master
branch](https://github.com/ZipCPU/eth10g/tree/master) has tended to have the
most recent updates.
