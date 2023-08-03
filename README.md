# An Open Source 10Gb Ethernet Switch

The main goal of this project is to demonstrate a 10Gb Ethernet switch.
Packets will arrive in one of four SFP+ interfaces, and from there be routed
as appropriately.

## Routing algorithm

The current (draft) routing algorithm is as follows:

1. For each incoming packet, its incoming port and source MAC address will be
   recorded in a table.

   - The table will have timeouts for all entries.
   - If the table is full, the new entry will overwrite the oldest entry

2. For each outgoing packet, if the destination MAC address matches the
   source address seen on a previous incoming source MAC address, the packet
   will be routed to that port.

3. In all other cases, if the port cannot be determined or if the destination
   port is to a broadcast address, the packet will be broadcast to all (other)
   ports.

4. One address will be reserved for a local soft-core CPU.

## Other hardware interfaces

Other hardware interfaces may also be present within this design, to include
UART, HDMI Tx and Rx, a SATA controller, micro SD, eMMC, QSPI flash, I2C,
temperature sensing and fan control, and much more.

- [UART console via the debugbus](rtl/wbubus/wbuconsole.v)
- [uSD](rtl/sdspi/sdspi.v) (SPI interface control only at present)
- [QSPI Flash](rtl/qflexpress.v)
- [I2C](rtl/wbi2c/wbi2ccpu.v)
  - Si5324 clock generator
  - B/W OLED display
- [SPIO: 5 buttons, 8 LEDs, and 9 switches](rtl/spio.v)
- HDMI RX and TX
- RPi CM4 SMI interface
- SATA
- EMMC

## Sponsorship

This is project is sponsored by Net Idea.

## License

This project is released under the Apache 2 license.

## Status

As of 15 May, 2023:

- The PCB for this project has been built, and is currently under test.

- The project RTL is partially assembled.  Components assembled, attached, and
  (potentially under test) include:
  - **Working:** The bus RTL has been assembled, to include the [Wishbone crossbar](rtl/wb2axip/rtl/wbxbar.v)s, as well as [up](rtl/wb2axip/wbupsz.v) and [down](rtl/wb2axip/wbdown.v) sizing components
  - **Working:** The [debug bus](https://github.com/ZipCPU/dbgbus), [the ZipCPU](https://github.com/ZipCPU/zipcpu), the [ZipCPU's (new) DMA](rtl/cpu/zipdma.v)
  - **Working:** The ZipCPU is running and working and (now) an integral part of testing.
  - **Working:** Several Wishbone Scopes have been used to debug things so far.
  - **Was working:** The [QSPI flash](rtl/qflexpress.v).  (The control wires
    have since been disconnected on the board, due to a conflict with the SDIO.
    This will be fixed in the next PCB revision.)
  - **Working:** The [I2C Controller](rtl/wbi2c/wbi2ccpu.v).
    - **Working:** [Fan control and temperature measurement](rtl/wbfan.v).  The I2C controller is used to sense temperature, as part of the [fan controller](rtl/wbfan.v)
    - **Working:** EDID information may be read from the downstream HDMI
    - **Working:** DDR3 configuration information may be read successfully from the DDR3 daughter board
    - (Working?)  SFP+ configuration information may also be read.
    - **Working:** [Si5324 reference clock controller](https://zipcpu.com/blog/2019/06/28/genclk.html).  That is, this clock can be configured.  I have yet to measure any clock output from this clock generator.
    - **Working:** [OLED display](https://www.amazon.com/Teyleten-Robot-Display-SSD1306-Raspberry/dp/B08ZY4YBHL/) via I2C

  - **Working:** [General](rtl/gpio.v) and [Special Purpose IO](rtl/spio.v) controllers
  - SD/eMMC:
    - **Working:** [SPI based SD card controller](https://github.com/ZipCPU/sdspi)
    - **Working:** [SDIO SD card controller](https://github.com/ZipCPU/sdspi).  Curiously, I marked the [SDSPI](https://github.com/ZipCPU/sdspi) controller as working too soon.  The SD data and command wires had no pullups.  This worked fine for the SDSPI controller, not for the [SDIO controller](https://github.com/ZipCPU/sdspi).  However, the [SDIO controller](https://github.com/ZipCPU/sdspi) is now working on the board after replacing one of the level shifting chips on the board.
    - The eMMC device, which also uses the [SDIO controller](https://github.com/ZipCPU/sdspi), is not yet working.
  - **(Sort of) Working:** [SMI Slave Controller](rtl/smi/smi.v).  The SMI pins appear to work--all except the SMI address pins.  I'm not sure why that is.
  - **Working:** [All buttons, switches, and LEDs](rtl/spio.v) are working.
  - **Working:** [HDMI transmitter](rtl/hdmi/vidpipe.v).  This is not part of the current integration, since the simulation for it didn't mix well with the CI/CD options under test.
  - The 10Gb Ethernet component is currently connected and undergoing test.

- Components not yet integrated include:
  - The [DDR3 SDRAM memory controller](https://github.com/AngeloJacobo/DDR3_Controller) has been ported to the board, but isn't yet working.
  - [The SATA Controller](https://github.com/ZipCPU/wbsata).
  - The HDMI receiver has been wired up for testing in the lab.  Success has not (yet) been demonstrated when using it.
