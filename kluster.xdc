## Define our clocks
## {{{
set_property -dict { PACKAGE_PIN AC9 IOSTANDARD DIFF_SSTL15 } [get_ports i_clk_200mhz_p]
set_property -dict { PACKAGE_PIN AD9 IOSTANDARD DIFF_SSTL15 } [get_ports i_clk_200mhz_n]
create_clock -period 5.0 -name SYSCLK -waveform { 0.0 2.50 } -add [get_ports i_clk_200mhz_p]

#set_property -dict { PACKAGE_PIN F6 } [get_ports i_clk_150mhz_p];	## 150MHz_REFCLK_P
#set_property -dict { PACKAGE_PIN F5 } [get_ports i_clk_150mhz_n];	## 150MHz_REFCLK_N
## The 150MHz clock will be declared in sata.txt, so it doesn't need to be
## declared here or now.
## create_clock -period 6.6666 -name SATAREF -waveform { 0.0 3.3333 } -add [get_ports i_clk_150mhz_p]

#set_property -dict { PACKAGE_PIN H6 } [get_ports i_clk_156mhz_p];	## 156.25MHz_REFCLK_P
#set_property -dict { PACKAGE_PIN H5 } [get_ports i_clk_156mhz_n];	## 156.25MHz_REFCLK_N
# create_clock -period 6.4 -name NETREF -waveform { 0.0 3.2 } -add [get_ports i_clk_156mhz_p]
create_clock -period 3.2 -name NETREF -waveform { 0.0 1.6 } -add [get_ports i_clk_156mhz_p]

#set_property -dict { PACKAGE_PIN K6 } [get_ports i_clk_si_p];		## SI5324_REFCLK_P
#set_property -dict { PACKAGE_PIN K5 } [get_ports i_clk_si_n];		## SI5324_REFCLK_P
## SIREF clock is declared in autodata/siclk.txt
create_clock -period 5.2 -name SIREF -waveform { 0.0 2.6 } -add [get_ports i_clk_si_p]

# 66 MHz clock input
#set_property -dict { PACKAGE_PIN E23 } [get_ports i_emcclk];					## FPGA_EMCCLK
#create_clock -period 15.14 -name EMCCLK -waveform { 0.0 7.57 } -add [get_ports i_clk_66mhz]

#set_property -dict { PACKAGE_PIN R21 IOSTANDARD TMDS_33 } [get_ports o_siref_clk_p]
#set_property -dict { PACKAGE_PIN P21 IOSTANDARD TMDS_33 } [get_ports o_siref_clk_n]

#set_property -dict { PACKAGE_PIN R21 IOSTANDARD LVCMOS33 } [get_ports io_siref_clk_p]
#set_property -dict { PACKAGE_PIN P21 IOSTANDARD LVCMOS33 } [get_ports io_siref_clk_n]

## }}}

## UART
## {{{
## UART IO standard is dependent upon CRUVI VSEL
#set_property -dict {PACKAGE_PIN A17 IOSTANDARD LVCMOS33} [get_ports o_wbu_uart_tx]
#set_property -dict {PACKAGE_PIN K15 IOSTANDARD LVCMOS33} [get_ports i_wbu_uart_rx]
#set_property -dict {PACKAGE_PIN B17 IOSTANDARD LVCMOS33} [get_ports i_wbu_uart_rts_n]
#set_property -dict {PACKAGE_PIN F18 IOSTANDARD LVCMOS33} [get_ports o_wbu_uart_cts_n]
## }}}

## Switches
## {{{
#set_property -dict {PACKAGE_PIN E25 IOSTANDARD LVCMOS18} [get_ports i_sw[0]]
#set_property -dict {PACKAGE_PIN E26 IOSTANDARD LVCMOS18} [get_ports i_sw[1]]
#set_property -dict {PACKAGE_PIN D25 IOSTANDARD LVCMOS18} [get_ports i_sw[2]]
#set_property -dict {PACKAGE_PIN F22 IOSTANDARD LVCMOS18} [get_ports i_sw[3]]
## Switches 4-8 do not appear to be present on v2
## #set_property -dict {PACKAGE_PIN D24 IOSTANDARD LVCMOS18} [get_ports i_sw[4]]
## #set_property -dict {PACKAGE_PIN D23 IOSTANDARD LVCMOS18} [get_ports i_sw[5]]
## #set_property -dict {PACKAGE_PIN E23 IOSTANDARD LVCMOS18} [get_ports i_sw[6]]
## #set_property -dict {PACKAGE_PIN E22 IOSTANDARD LVCMOS18} [get_ports i_sw[7]]
## #set_property -dict {PACKAGE_PIN J25 IOSTANDARD LVCMOS18} [get_ports i_sw[8]]
## }}}

## Buttons
## {{{
#set_property -dict {PACKAGE_PIN J24 IOSTANDARD LVCMOS18} [get_ports i_nbtn_u]
#set_property -dict {PACKAGE_PIN H22 IOSTANDARD LVCMOS18} [get_ports i_nbtn_l]
#set_property -dict {PACKAGE_PIN H23 IOSTANDARD LVCMOS18} [get_ports i_nbtn_c]
#set_property -dict {PACKAGE_PIN H24 IOSTANDARD LVCMOS18} [get_ports i_nbtn_r]
#set_property -dict {PACKAGE_PIN G22 IOSTANDARD LVCMOS18} [get_ports i_nbtn_d]
## }}}

## LEDs
## {{{
#set_property -dict {PACKAGE_PIN F23 IOSTANDARD LVCMOS18} [get_ports o_led[0]]
#set_property -dict {PACKAGE_PIN J26 IOSTANDARD LVCMOS18} [get_ports o_led[1]]
#set_property -dict {PACKAGE_PIN G26 IOSTANDARD LVCMOS18} [get_ports o_led[2]]
#set_property -dict {PACKAGE_PIN H26 IOSTANDARD LVCMOS18} [get_ports o_led[3]]
#set_property -dict {PACKAGE_PIN G25 IOSTANDARD LVCMOS18} [get_ports o_led[4]]
#set_property -dict {PACKAGE_PIN F24 IOSTANDARD LVCMOS18} [get_ports o_led[5]]
#set_property -dict {PACKAGE_PIN F25 IOSTANDARD LVCMOS18} [get_ports o_led[6]]
#set_property -dict {PACKAGE_PIN G24 IOSTANDARD LVCMOS18} [get_ports o_led[7]]
## }}}

## FAN control
## {{{
## FAN IO standard is dependent upon CRUVI VSEL
#set_property -dict {PACKAGE_PIN B19 IOSTANDARD LVCMOS33} [get_ports i_fan_tach];	## FPGA_FAN_TACH
#set_property -dict {PACKAGE_PIN C17 IOSTANDARD LVCMOS33} [get_ports o_fan_pwm];		## FPGA_FAN_PWM
#set_property -dict {PACKAGE_PIN C19 IOSTANDARD LVCMOS33} [get_ports o_fan_sys];		## SYS_FAN_PWM
## }}}

## External resets
## {{{
#set_property -dict {PACKAGE_PIN U16 IOSTANDARD LVCMOS33} [get_ports i_pi_reset_n];	# PI_EXTRST
#set_property -dict {PACKAGE_PIN A20 IOSTANDARD LVCMOS18} [get_ports i_soft_reset];	# FPGA SOFT RST (User button)
## }}}

## I2C
## {{{
#set_property -dict {PACKAGE_PIN W21  IOSTANDARD LVCMOS18} [get_ports o_i2c_mxrst_n];		## Main_I2C_MUX_RST
#set_property -dict {PACKAGE_PIN V21  IOSTANDARD LVCMOS18} [get_ports io_i2c_scl];		## Main_I2C_SCL
#set_property -dict {PACKAGE_PIN AE22 IOSTANDARD LVCMOS18} [get_ports io_i2c_sda];		## MAIN_I2C_SDA
#set_property -dict {PACKAGE_PIN AE26 IOSTANDARD LVCMOS18} [get_ports io_temp_scl];		## TEMP_I2C_SCL_LS
#set_property -dict {PACKAGE_PIN AD26 IOSTANDARD LVCMOS18} [get_ports io_temp_sda];		## TEMP_I2C_SDA_LS
#set_property -dict {PACKAGE_PIN V24  IOSTANDARD LVCMOS18} [get_ports i_si5324_int];		## Si5324_INIT_LS
#set_property -dict {PACKAGE_PIN V22  IOSTANDARD LVCMOS18} [get_ports o_si5324_rst];		## Si5324_RST_LS

#set_property -dict {PACKAGE_PIN AB25 IOSTANDARD LVCMOS18} [get_ports io_cm4_sda];		## CM4_SDA, CM4_GPIO00
#set_property -dict {PACKAGE_PIN V23  IOSTANDARD LVCMOS18} [get_ports io_cm4_scl];		## CM4_SCL, CM4_GPIO01
## }}}

## ETH10G
## {{{
## LOS
#set_property -dict {PACKAGE_PIN T19 IOSTANDARD LVCMOS33} [get_ports i_gnet_los[0]]
#set_property -dict {PACKAGE_PIN M19 IOSTANDARD LVCMOS33} [get_ports i_gnet_los[1]]
#set_property -dict {PACKAGE_PIN R17 IOSTANDARD LVCMOS33} [get_ports i_gnet_los[2]]
#set_property -dict {PACKAGE_PIN R16 IOSTANDARD LVCMOS33} [get_ports i_gnet_los[3]]

## TX Disable
#set_property -dict {PACKAGE_PIN R18 IOSTANDARD LVCMOS33} [get_ports o_gnettx_disable[0]];	## SFP+_0_TX_EN
#set_property -dict {PACKAGE_PIN N18 IOSTANDARD LVCMOS33} [get_ports o_gnettx_disable[1]];	## SFP+_1_TX_EN
#set_property -dict {PACKAGE_PIN N17 IOSTANDARD LVCMOS33} [get_ports o_gnettx_disable[2]];	## SFP+_2_TX_EN
#set_property -dict {PACKAGE_PIN P16 IOSTANDARD LVCMOS33} [get_ports o_gnettx_disable[3]];	## SFP+_3_TX_EN

## LinkUp LEDs
#set_property -dict {PACKAGE_PIN T24 IOSTANDARD LVCMOS33} [get_ports o_gnet_linkup[0]];		## SFP+_0_Link
#set_property -dict {PACKAGE_PIN T22 IOSTANDARD LVCMOS33} [get_ports o_gnet_linkup[1]];		## SFP+_1_Link
#set_property -dict {PACKAGE_PIN N22 IOSTANDARD LVCMOS33} [get_ports o_gnet_linkup[2]];		## SFP+_2_Link
#set_property -dict {PACKAGE_PIN R20 IOSTANDARD LVCMOS33} [get_ports o_gnet_linkup[3]];		## SFP+_3_Link

## Activity LEDs
#set_property -dict {PACKAGE_PIN T25 IOSTANDARD LVCMOS33} [get_ports o_gnet_activity[0]];	## SFP+_0_ACT
#set_property -dict {PACKAGE_PIN R23 IOSTANDARD LVCMOS33} [get_ports o_gnet_activity[1]];	## SFP+_1_ACT
#set_property -dict {PACKAGE_PIN N21 IOSTANDARD LVCMOS33} [get_ports o_gnet_activity[2]];	## SFP+_2_ACT
#set_property -dict {PACKAGE_PIN R22 IOSTANDARD LVCMOS33} [get_ports o_gnet_activity[3]];	## SFP+_3_ACT

## Network transmit/outputs
#set_property -dict {PACKAGE_PIN P2} [get_ports o_gnet_p[0]];	## MGTX115_TX0_P
#set_property -dict {PACKAGE_PIN P1} [get_ports o_gnet_n[0]];	## MGTX115_TX0_N
#set_property -dict {PACKAGE_PIN M2} [get_ports o_gnet_p[1]];	## MGTX115_TX1_P
#set_property -dict {PACKAGE_PIN M1} [get_ports o_gnet_n[1]];	## MGTX115_TX1_N
#set_property -dict {PACKAGE_PIN K2} [get_ports o_gnet_p[2]];	## MGTX115_TX2_P
#set_property -dict {PACKAGE_PIN K1} [get_ports o_gnet_n[2]];	## MGTX115_TX2_N
#set_property -dict {PACKAGE_PIN H2} [get_ports o_gnet_p[3]];	## MGTX115_TX3_P
#set_property -dict {PACKAGE_PIN H1} [get_ports o_gnet_n[3]];	## MGTX115_TX3_N

## Network receive/input
#set_property -dict {PACKAGE_PIN R4} [get_ports i_gnet_p[0]];	## MGTX115_RX0_P
#set_property -dict {PACKAGE_PIN R3} [get_ports i_gnet_n[0]];	## MGTX115_RX0_N
#set_property -dict {PACKAGE_PIN N4} [get_ports i_gnet_p[1]];	## MGTX115_RX1_P
#set_property -dict {PACKAGE_PIN N3} [get_ports i_gnet_n[1]];	## MGTX115_RX1_N
#set_property -dict {PACKAGE_PIN L4} [get_ports i_gnet_p[2]];	## MGTX115_RX2_P
#set_property -dict {PACKAGE_PIN L3} [get_ports i_gnet_n[2]];	## MGTX115_RX2_N
#set_property -dict {PACKAGE_PIN J4} [get_ports i_gnet_p[3]];	## MGTX115_RX3_P
#set_property -dict {PACKAGE_PIN J3} [get_ports i_gnet_n[3]];	## MGTX115_RX3_N
## }}}

## CM4-GPIO
## {{{
#set_property -dict {PACKAGE_PIN AB25 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 0]];		## CM4_SDA
#set_property -dict {PACKAGE_PIN V23  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 1]];		## CM4_SCL
#set_property -dict {PACKAGE_PIN U26  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 2]]
#set_property -dict {PACKAGE_PIN U24  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 3]]
#set_property -dict {PACKAGE_PIN V26  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 4]]
#set_property -dict {PACKAGE_PIN AB26 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 5]]
#set_property -dict {PACKAGE_PIN AC24 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 6]]
#set_property -dict {PACKAGE_PIN W23  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 7]];		## CM4_CS[1]
#set_property -dict {PACKAGE_PIN W24  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 8]];		## CM4_CS[0]
#set_property -dict {PACKAGE_PIN Y26  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[ 9]];		## CM4_MISO
#set_property -dict {PACKAGE_PIN Y25  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[10]];		## CM4_MOSI
#set_property -dict {PACKAGE_PIN AA25 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[11]];		## CM4_SCK
#set_property -dict {PACKAGE_PIN U22  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[12]];		## CM4_PWM[0]
#set_property -dict {PACKAGE_PIN AC26 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[13]];		## CM4_PWM[1]
#set_property -dict {PACKAGE_PIN U25  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[14]];		## CM4_UART_TX
#set_property -dict {PACKAGE_PIN W26  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[15]];		## CM4_UART_RX
#set_property -dict {PACKAGE_PIN Y22  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[16]]
#set_property -dict {PACKAGE_PIN W25  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[17]]
#set_property -dict {PACKAGE_PIN Y23  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[18]];		## CM4_I2S_CLK
#set_property -dict {PACKAGE_PIN AC23 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[19]];		## CM4_I2S_FS
#set_property -dict {PACKAGE_PIN Y21  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[20]];		## CM4_I2S_DIN
#set_property -dict {PACKAGE_PIN W20  IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[21]];		## CM4_I2S_DOUT
#set_property -dict {PACKAGE_PIN W26 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[22]];		## CM4_SDSLV_CLK
#set_property -dict {PACKAGE_PIN AA23 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[23]];		## CM4_SDSLV_CMD
#set_property -dict {PACKAGE_PIN AA24 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[24]];		## CM4_SDSLV_D[0]
#set_property -dict {PACKAGE_PIN AA22 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[25]];		## CM4_SDSLV_D[1]
#set_property -dict {PACKAGE_PIN AF24 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[26]];		## CM4_SDSLV_D[2]
#set_property -dict {PACKAGE_PIN AF25 IOSTANDARD LVCMOS18} [get_ports io_cm4_gpio[27]];		## CM4_SDSLV_D[3]
## }}}

## CM4-UART
## {{{
#set_property -dict {PACKAGE_PIN U25  IOSTANDARD LVCMOS18} [get_ports i_cm4_uart];		## CM4_UART_TX, CM4_GPIO14
#set_property -dict {PACKAGE_PIN AB24  IOSTANDARD LVCMOS18} [get_ports o_cm4_uart];		## CM4_UART_RX, CM4_GPIO15
#set_property -dict {PACKAGE_PIN Y22  IOSTANDARD LVCMOS18} [get_ports i_cm4_cts_n];		## CM4_UART_CTS, CM4_GPIO16
#set_property -dict {PACKAGE_PIN W25  IOSTANDARD LVCMOS18} [get_ports i_cm4_rts_n];		## CM4_UART_RTS, CM4_GPIO17
## }}}

## CM4-SPI
## {{{
#set_property -dict {PACKAGE_PIN W23  IOSTANDARD LVCMOS18} [get_ports i_cm4_spi_cs[1]];		## CM4_CS[1], CM4_GPIO07
#set_property -dict {PACKAGE_PIN W24  IOSTANDARD LVCMOS18} [get_ports i_cm4_spi_cs[0]];		## CM4_CS[0], CM4_GPIO08
#set_property -dict {PACKAGE_PIN Y26  IOSTANDARD LVCMOS18} [get_ports o_cm4_spi_miso];		## CM4_MISO, CM4_GPIO09
#set_property -dict {PACKAGE_PIN Y25  IOSTANDARD LVCMOS18} [get_ports i_cm4_spi_mosi];		## CM4_MOSI, CM4_GPIO10
#set_property -dict {PACKAGE_PIN AA25 IOSTANDARD LVCMOS18} [get_ports i_cm4_spi_sck];		## CM4_SCK, CM4_GPIO11
## }}}

## CM4-PWM
## {{{
#set_property -dict {PACKAGE_PIN U22  IOSTANDARD LVCMOS18} [get_ports i_cm4_pwm[0]];		## CM4_PWM[0], CM4_GPIO12
#set_property -dict {PACKAGE_PIN AC26 IOSTANDARD LVCMOS18} [get_ports i_cm4_pwm[1]];		## CM4_PWM[1], CM4_GPIO13
## }}}

## I2S-Slv
## {{{
#set_property -dict {PACKAGE_PIN Y23  IOSTANDARD LVCMOS18} [get_ports i_i2s_clk];		## CM4_I2S_CLK, CM4_GPIO18
#set_property -dict {PACKAGE_PIN AC23 IOSTANDARD LVCMOS18} [get_ports i_i2s_fs];			## CM4_I2S_FS, CM4_GPIO19
#set_property -dict {PACKAGE_PIN Y21  IOSTANDARD LVCMOS18} [get_ports i_i2s_din];		## CM4_I2S_DIN, CM4_GPIO20
#set_property -dict {PACKAGE_PIN W20  IOSTANDARD LVCMOS18} [get_ports o_i2s_dout];		## CM4_I2S_DOUT, CM4_GPIO21
## }}}

## SDSLV
## {{{
#set_property -dict {PACKAGE_PIN W26 IOSTANDARD LVCMOS18} [get_ports i_sdslav_clk];		## CM4_SDSLV_CLK, CM4_GPIO22
#set_property -dict {PACKAGE_PIN AA23 IOSTANDARD LVCMOS18} [get_ports io_sdslav_cmd];		## CM4_SDSLV_CMD, CM4_GPIO23
#set_property -dict {PACKAGE_PIN AA24 IOSTANDARD LVCMOS18} [get_ports io_sdslav_dat[0]];		## CM4_SDSLV_D[0], CM4_GPIO24
#set_property -dict {PACKAGE_PIN AA22 IOSTANDARD LVCMOS18} [get_ports io_sdslav_dat[1]];		## CM4_SDSLV_D[1], CM4_GPIO25
#set_property -dict {PACKAGE_PIN AF24 IOSTANDARD LVCMOS18} [get_ports io_sdslav_dat[2]];		## CM4_SDSLV_D[2], CM4_GPIO26
#set_property -dict {PACKAGE_PIN AF25 IOSTANDARD LVCMOS18} [get_ports io_sdslav_dat[3]];		## CM4_SDSLV_D[3], CM4_GPIO27
## }}}

## uSD
## {{{
#set_property -dict {PACKAGE_PIN AE21 IOSTANDARD LVCMOS18} [get_ports i_sdcard_clk_fb]
#set_property -dict {PACKAGE_PIN AC22 IOSTANDARD LVCMOS18} [get_ports i_sdcard_cd_n];		## SDCARD.CD
#set_property -dict {PACKAGE_PIN AD21 IOSTANDARD LVCMOS18} [get_ports o_sdcard_clk];		## SDCARD.CLK
#set_property -dict {PACKAGE_PIN AB22 IOSTANDARD LVCMOS18} [get_ports io_sdcard_cmd]
#set_property -dict {PACKAGE_PIN AD24 IOSTANDARD LVCMOS18} [get_ports io_sdcard_dat[0]]
#set_property -dict {PACKAGE_PIN AC21 IOSTANDARD LVCMOS18} [get_ports io_sdcard_dat[1]]
#set_property -dict {PACKAGE_PIN AD23 IOSTANDARD LVCMOS18} [get_ports io_sdcard_dat[2]]
#set_property -dict {PACKAGE_PIN AB21 IOSTANDARD LVCMOS18} [get_ports io_sdcard_dat[3]]

#set_property -dict {PACKAGE_PIN AD25} [get_ports o_uhs_ck_p];		## Also called SDCARD.RCLK_P
#set_property -dict {PACKAGE_PIN AE25} [get_ports o_uhs_ck_p];		## Also called SDCARD.RCLK_N
#set_property -dict {PACKAGE_PIN F2}   [get_ports o_uhs_sd_p];		## SDCARD_PETX_P
#set_property -dict {PACKAGE_PIN F1}   [get_ports o_uhs_sd_n];		## SDCARD_PETX_N
#set_property -dict {PACKAGE_PIN G4}   [get_ports i_uhs_sd_p];		## SDCARD_PERX_P
#set_property -dict {PACKAGE_PIN G3}   [get_ports i_uhs_sd_n];		## SDCARD_PERX_N

#set_property -dict {PACKAGE_PIN Y20  IOSTANDARD LVCMOS18} [get_ports o_sdcard_wp]
#set_property -dict {PACKAGE_PIN AF23 IOSTANDARD LVCMOS18} [get_ports o_sdcard_en];	## Powers the card
#set_property -dict {PACKAGE_PIN AE23 IOSTANDARD LVCMOS18} [get_ports o_sdcard_mux];	## Controls RCLK/D[1:0] MX
#set_property -dict {PACKAGE_PIN AF22 IOSTANDARD LVCMOS18} [get_ports o_sdcard_vsel];	## 0=1.8V, 1=3.3V
## }}}

## Flash
## {{{
## The flash clock pin is (also on) CCLK_0 / C8
#set_property -dict {PACKAGE_PIN B26 IOSTANDARD LVCMOS18} [get_ports o_flash_sck]
#set_property -dict {PACKAGE_PIN C23 IOSTANDARD LVCMOS18} [get_ports o_flash_cs_n]

#set_property -dict {PACKAGE_PIN B24 IOSTANDARD LVCMOS18} [get_ports io_flash_dat[0]]
#set_property -dict {PACKAGE_PIN A25 IOSTANDARD LVCMOS18} [get_ports io_flash_dat[1]]
#set_property -dict {PACKAGE_PIN B22 IOSTANDARD LVCMOS18} [get_ports io_flash_dat[2]]
#set_property -dict {PACKAGE_PIN A22 IOSTANDARD LVCMOS18} [get_ports io_flash_dat[3]]
## }}}

## eMMC
## {{{
#set_property -dict {PACKAGE_PIN D23 IOSTANDARD LVCMOS18} [get_ports o_emmc_clk]
#set_property -dict {PACKAGE_PIN E22 IOSTANDARD LVCMOS18} [get_ports io_emmc_cmd]

#set_property -dict {PACKAGE_PIN A24 IOSTANDARD LVCMOS18} [get_ports io_emmc_dat[0]]
#set_property -dict {PACKAGE_PIN A23 IOSTANDARD LVCMOS18} [get_ports io_emmc_dat[1]]
#set_property -dict {PACKAGE_PIN C26 IOSTANDARD LVCMOS18} [get_ports io_emmc_dat[2]]
#set_property -dict {PACKAGE_PIN D21 IOSTANDARD LVCMOS18} [get_ports io_emmc_dat[3]]
#set_property -dict {PACKAGE_PIN C24 IOSTANDARD LVCMOS18} [get_ports io_emmc_dat[4]]
#set_property -dict {PACKAGE_PIN C21 IOSTANDARD LVCMOS18} [get_ports io_emmc_dat[5]]
#set_property -dict {PACKAGE_PIN D24 IOSTANDARD LVCMOS18} [get_ports io_emmc_dat[6]]
#set_property -dict {PACKAGE_PIN B21 IOSTANDARD LVCMOS18} [get_ports io_emmc_dat[7]]
#set_property -dict {PACKAGE_PIN C22 IOSTANDARD LVCMOS18} [get_ports i_emmc_ds]
#set_property -dict {PACKAGE_PIN D26 IOSTANDARD LVCMOS18} [get_ports o_emmc_reset_n]
## }}}

## SATA
## {{{
#set_property -dict {PACKAGE_PIN B2} [get_ports o_sata_p];	## SATA_TX_C_P
#set_property -dict {PACKAGE_PIN B1} [get_ports o_sata_n];	## SATA_TX_C_N
#set_property -dict {PACKAGE_PIN C4} [get_ports i_sata_p];	## SATA_RX_C_P
#set_property -dict {PACKAGE_PIN C3} [get_ports i_sata_n];	## SATA_RX_C_N
## }}}

## DDR3
## {{{
#set_property -dict {PACKAGE_PIN V11  IOSTANDARD LVCMOS15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_reset_n];	#
#set_property -dict {PACKAGE_PIN AB11 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_clk_p];	#
#set_property -dict {PACKAGE_PIN AC11 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_clk_n];	#
#set_property -dict {PACKAGE_PIN AA9  IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_clk_p_1];	#
#set_property -dict {PACKAGE_PIN AB9  IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_clk_n_1];	#
#set_property -dict {PACKAGE_PIN Y10  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_cke[0]];	#
#set_property -dict {PACKAGE_PIN W9   IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_cke[1]];	#

#set_property -dict {PACKAGE_PIN AA10 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_ras_n];	#
#set_property -dict {PACKAGE_PIN AA7  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_cas_n];	#
#set_property -dict {PACKAGE_PIN Y7   IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_we_n];	#
#set_property -dict {PACKAGE_PIN Y8   IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_s_n[0]];	#
#set_property -dict {PACKAGE_PIN V7   IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_s_n[1]];	#
#set_property -dict {PACKAGE_PIN AA8  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_odt[0]]
#set_property -dict {PACKAGE_PIN V9   IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_odt[1]]
#set_property -dict {PACKAGE_PIN W10  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports i_ddr3_event]

### Address lines
### {{{
#set_property -dict {PACKAGE_PIN AC7  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_ba[0]];	#
#set_property -dict {PACKAGE_PIN V8   IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_ba[1]];	#
#set_property -dict {PACKAGE_PIN AC13 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_ba[2]];	#

#set_property -dict {PACKAGE_PIN AF7  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[0]]
#set_property -dict {PACKAGE_PIN AD8  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[1]]
#set_property -dict {PACKAGE_PIN AB10 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[2]]
#set_property -dict {PACKAGE_PIN AC8  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[3]]
#set_property -dict {PACKAGE_PIN W11  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[4]];	#
#set_property -dict {PACKAGE_PIN AA12 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[5]]
#set_property -dict {PACKAGE_PIN AC12 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[6]]
#set_property -dict {PACKAGE_PIN AD13 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[7]]

#set_property -dict {PACKAGE_PIN AB12 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[8]]
#set_property -dict {PACKAGE_PIN AD11 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[9]]
#set_property -dict {PACKAGE_PIN AE7  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[10]]
#set_property -dict {PACKAGE_PIN Y11  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[11]];	#
#set_property -dict {PACKAGE_PIN AA13 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[12]]
#set_property -dict {PACKAGE_PIN AB7  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[13]]
#set_property -dict {PACKAGE_PIN Y13  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[14]]
#set_property -dict {PACKAGE_PIN Y12  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_a[15]]
### }}}

### Byte lane #0
### {{{
#set_property -dict {PACKAGE_PIN AB17 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[0]]
#set_property -dict {PACKAGE_PIN AC18 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[1]]
#set_property -dict {PACKAGE_PIN AC17 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[2]]
#set_property -dict {PACKAGE_PIN AD19 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[3]]
#set_property -dict {PACKAGE_PIN AA19 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[4]]
#set_property -dict {PACKAGE_PIN AA20 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[5]]
#set_property -dict {PACKAGE_PIN AD18 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[6]]
#set_property -dict {PACKAGE_PIN AC16 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[7]]
#set_property -dict {PACKAGE_PIN AD20 IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_p[0]]
#set_property -dict {PACKAGE_PIN AE20 IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_n[0]]
#set_property -dict {PACKAGE_PIN AC19 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_dm[0]]
### }}}

### Byte lane #1
### {{{
#set_property -dict {PACKAGE_PIN V16  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[8]]
#set_property -dict {PACKAGE_PIN V18  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[9]]
#set_property -dict {PACKAGE_PIN AB20  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[10]]
#set_property -dict {PACKAGE_PIN AB19  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[11]]
#set_property -dict {PACKAGE_PIN W15  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[12]]
#set_property -dict {PACKAGE_PIN V19  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[13]]
#set_property -dict {PACKAGE_PIN W16  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[14]]
#set_property -dict {PACKAGE_PIN Y17  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[15]]
#set_property -dict {PACKAGE_PIN W18  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_p[1]]
#set_property -dict {PACKAGE_PIN W19  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_n[1]]
#set_property -dict {PACKAGE_PIN V17  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_dm[1]]
### }}}

### Byte lane #2
### {{{
#set_property -dict {PACKAGE_PIN AF19  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[16]]
#set_property -dict {PACKAGE_PIN AE17  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[17]]
#set_property -dict {PACKAGE_PIN AE15  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[18]]
#set_property -dict {PACKAGE_PIN AF15  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[19]]
#set_property -dict {PACKAGE_PIN AF20  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[20]]
#set_property -dict {PACKAGE_PIN AD16  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[21]]
#set_property -dict {PACKAGE_PIN AD15  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[22]]
#set_property -dict {PACKAGE_PIN AF14  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[23]]
#set_property -dict {PACKAGE_PIN AE18  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_p[2]]
#set_property -dict {PACKAGE_PIN AF18  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_n[2]]
#set_property -dict {PACKAGE_PIN AF17  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_dm[2]]
### }}}

### Byte lane #3
### {{{
#set_property -dict {PACKAGE_PIN AA15 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[24]]
#set_property -dict {PACKAGE_PIN AB16 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[25]]
#set_property -dict {PACKAGE_PIN AD14 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[26]]
#set_property -dict {PACKAGE_PIN AB14 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[27]]
#set_property -dict {PACKAGE_PIN AA18 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[28]]
#set_property -dict {PACKAGE_PIN AA17 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[29]]
#set_property -dict {PACKAGE_PIN AB15 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[30]]
#set_property -dict {PACKAGE_PIN AC14 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[31]]
#set_property -dict {PACKAGE_PIN Y15  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_p[3]]
#set_property -dict {PACKAGE_PIN Y16  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_n[3]]
#set_property -dict {PACKAGE_PIN AA14 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_dm[3]]
### }}}

### Byte lane #4
### {{{
#set_property -dict {PACKAGE_PIN AD6 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[32]]
#set_property -dict {PACKAGE_PIN AC6 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[33]]
#set_property -dict {PACKAGE_PIN AC3 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[34]]
#set_property -dict {PACKAGE_PIN AB4 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[35]]
#set_property -dict {PACKAGE_PIN AB6 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[36]]
#set_property -dict {PACKAGE_PIN Y6  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[37]]
#set_property -dict {PACKAGE_PIN Y5  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[38]]
#set_property -dict {PACKAGE_PIN AA4 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[39]]
#set_property -dict {PACKAGE_PIN AA5 IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_p[4]]
#set_property -dict {PACKAGE_PIN AB5 IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_n[4]]
#set_property -dict {PACKAGE_PIN AC4 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_dm[4]]
### }}}

### Byte lane #5
### {{{
#set_property -dict {PACKAGE_PIN AF3  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[40]]
#set_property -dict {PACKAGE_PIN AE3  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[41]]
#set_property -dict {PACKAGE_PIN AE2  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[42]]
#set_property -dict {PACKAGE_PIN AE1  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[43]]
#set_property -dict {PACKAGE_PIN AE6  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[44]]
#set_property -dict {PACKAGE_PIN AE5  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[45]]
#set_property -dict {PACKAGE_PIN AD4  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[46]]
#set_property -dict {PACKAGE_PIN AD1  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[47]]
#set_property -dict {PACKAGE_PIN AF5  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_p[5]]
#set_property -dict {PACKAGE_PIN AF4  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_n[5]]
#set_property -dict {PACKAGE_PIN AF2  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_dm[5]]
### }}}

### Byte lane #6
### {{{
#set_property -dict {PACKAGE_PIN W3  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[48]]
#set_property -dict {PACKAGE_PIN V4  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[49]]
#set_property -dict {PACKAGE_PIN U2  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[50]]
#set_property -dict {PACKAGE_PIN U5  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[51]]
#set_property -dict {PACKAGE_PIN V6  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[52]]
#set_property -dict {PACKAGE_PIN V3  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[53]]
#set_property -dict {PACKAGE_PIN U1  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[54]]
#set_property -dict {PACKAGE_PIN U6  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[55]]
#set_property -dict {PACKAGE_PIN W6  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_p[6]]
#set_property -dict {PACKAGE_PIN W5  IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_n[6]]
#set_property -dict {PACKAGE_PIN U7  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_dm[6]]
### }}}

### Byte lane #7
### {{{
#set_property -dict {PACKAGE_PIN AB2 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[56]]
#set_property -dict {PACKAGE_PIN AA3 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[57]]
#set_property -dict {PACKAGE_PIN W1  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[58]]
#set_property -dict {PACKAGE_PIN V2  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[59]]
#set_property -dict {PACKAGE_PIN AC2 IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[60]]
#set_property -dict {PACKAGE_PIN Y3  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[61]]
#set_property -dict {PACKAGE_PIN Y2  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[62]]
#set_property -dict {PACKAGE_PIN V1  IOSTANDARD SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dq[63]]
#set_property -dict {PACKAGE_PIN AB1 IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_p[7]]
#set_property -dict {PACKAGE_PIN AC1 IOSTANDARD DIFF_SSTL15_T_DCI SLEW FAST VCCAUX_IO HIGH} [get_ports io_ddr3_dqs_n[7]]
#set_property -dict {PACKAGE_PIN Y1  IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports o_ddr3_dm[7]]
### }}}

## }}}

## HDMI
## {{{
#set_property -dict {PACKAGE_PIN L24 IOSTANDARD LVCMOS33} [get_ports io_hdmirx_cec]
#set_property -dict {PACKAGE_PIN M22 IOSTANDARD LVCMOS33} [get_ports o_hdmirx_hpd_n]
#set_property -dict {PACKAGE_PIN M24 IOSTANDARD LVCMOS33} [get_ports io_hdmirx_scl]
#set_property -dict {PACKAGE_PIN M21 IOSTANDARD LVCMOS33} [get_ports io_hdmirx_sda]

#set_property -dict {PACKAGE_PIN P24 IOSTANDARD TMDS_33} [get_ports i_hdmirx_p[0]]
#set_property -dict {PACKAGE_PIN N24 IOSTANDARD TMDS_33} [get_ports i_hdmirx_n[0]]
#set_property -dict {PACKAGE_PIN R26 IOSTANDARD TMDS_33} [get_ports i_hdmirx_p[1]]
#set_property -dict {PACKAGE_PIN P26 IOSTANDARD TMDS_33} [get_ports i_hdmirx_n[1]]
#set_property -dict {PACKAGE_PIN R25 IOSTANDARD TMDS_33} [get_ports i_hdmirx_p[2]]
#set_property -dict {PACKAGE_PIN P25 IOSTANDARD TMDS_33} [get_ports i_hdmirx_n[2]]
#set_property -dict {PACKAGE_PIN P23 IOSTANDARD TMDS_33} [get_ports i_hdmirx_clk_p]
#set_property -dict {PACKAGE_PIN N23 IOSTANDARD TMDS_33} [get_ports i_hdmirx_clk_n]

#set_property -dict {PACKAGE_PIN N26 IOSTANDARD LVCMOS33} [get_ports io_hdmitx_cec]
#set_property -dict {PACKAGE_PIN M26 IOSTANDARD LVCMOS33} [get_ports i_hdmitx_hpd_n]

#set_property -dict {PACKAGE_PIN P19 IOSTANDARD TMDS_33} [get_ports o_hdmitx_p[0]]
#set_property -dict {PACKAGE_PIN P20 IOSTANDARD TMDS_33} [get_ports o_hdmitx_n[0]]
#set_property -dict {PACKAGE_PIN K25 IOSTANDARD TMDS_33} [get_ports o_hdmitx_p[1]]
#set_property -dict {PACKAGE_PIN K26 IOSTANDARD TMDS_33} [get_ports o_hdmitx_n[1]]
#set_property -dict {PACKAGE_PIN M25 IOSTANDARD TMDS_33} [get_ports o_hdmitx_p[2]]
#set_property -dict {PACKAGE_PIN L25 IOSTANDARD TMDS_33} [get_ports o_hdmitx_n[2]]
#set_property -dict {PACKAGE_PIN N19 IOSTANDARD TMDS_33} [get_ports o_hdmitx_clk_p]
#set_property -dict {PACKAGE_PIN M20 IOSTANDARD TMDS_33} [get_ports o_hdmitx_clk_n]
## }}}

## PCIe
## {{{
#set_property -dict { PACKAGE_PIN D6  IOSTANDARD DIFF_HSTL_I_10 } [get_ports o_pcie_clk_p];	# PCIe_REFCLK_P
#set_property -dict { PACKAGE_PIN D5  IOSTANDARD DIFF_HSTL_I_10 } [get_ports o_pcie_clk_n];	# PCIe_REFCLK_N
#set_property -dict { PACKAGE_PIN P18 IOSTANDARD DIFF_HSTL_I_10 } [get_ports o_pcie_perst_n]

#set_property -dict {PACKAGE_PIN A4 IOSTANDARD DIFF_HSTL_I_10 [get_ports o_pcie_p];	# PCIe_C_Tx0_P
#set_property -dict {PACKAGE_PIN A3 IOSTANDARD DIFF_HSTL_I_10 [get_ports o_pcie_n];	# PCIe_C_Tx0_N
#set_property -dict {PACKAGE_PIN B6 IOSTANDARD DIFF_HSTL_I_10 [get_ports i_pcie_p];	# PCIe_RX0_P
#set_property -dict {PACKAGE_PIN B5 IOSTANDARD DIFF_HSTL_I_10 [get_ports i_pcie_n];	# PCIe_RX0_N
## }}}

## VCC-CRUVI
## {{{
##		ADJ1	ADJ2	ADJ3	ADJ4
##	1.2V	0	0	0	0
##	1.5V	1	0	0	0
##	1.8V	x	1	0	0
##	2.5V	x	x	1	0
##	3.3V	x	x	x	1
##
## This controls *ALL* the CRUVI voltage levels, as well as the UART and FAN levels.
## The CRUVI IO standards defined within depend upon o_cruvi_vsel = 4'h8
##
#set_property -dict {PACKAGE_PIN T23 IOSTANDARD LVCMOS33} [get_ports o_cruvi_vsel[0]]];	## VSEL.ADJ1
#set_property -dict {PACKAGE_PIN T20 IOSTANDARD LVCMOS33} [get_ports o_cruvi_vsel[1]]];	## VSEL.ADJ2
#set_property -dict {PACKAGE_PIN U17 IOSTANDARD LVCMOS33} [get_ports o_cruvi_vsel[2]]];	## VSEL.ADJ3
#set_property -dict {PACKAGE_PIN T18 IOSTANDARD LVCMOS33} [get_ports o_cruvi_vsel[3]]];	## VSEL.ADJ4
## }}}

## CRUVI-A
## {{{
#set_property -dict {PACKAGE_PIN H19 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_SMB_ALERT]]
#set_property -dict {PACKAGE_PIN H18 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_HSIO]]
#set_property -dict {PACKAGE_PIN H16 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_RESET]]
#set_property -dict {PACKAGE_PIN F17 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_HSI]]
#set_property -dict {PACKAGE_PIN H17 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_HSO]]
#set_property -dict {PACKAGE_PIN F19 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_SMB_SDA]]
#set_property -dict {PACKAGE_PIN G17 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_SMB_SCL]]
#set_property -dict {PACKAGE_PIN E17 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_REFCLK]]
#set_property -dict {PACKAGE_PIN F9 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_0_P]]
#set_property -dict {PACKAGE_PIN F8 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_0_N]]
#set_property -dict {PACKAGE_PIN B14 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_1_P]]
#set_property -dict {PACKAGE_PIN A14 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_1_N]]
#set_property -dict {PACKAGE_PIN B15 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_2_P]]
#set_property -dict {PACKAGE_PIN A14 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_2_N]]
#set_property -dict {PACKAGE_PIN C14  IOSTANDARD LVCMOS33} [get_ports CRUVI_A_3_P]]
#set_property -dict {PACKAGE_PIN C13 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_3_N]]
#set_property -dict {PACKAGE_PIN D14 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_4_P]]
#set_property -dict {PACKAGE_PIN D13 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_4_N]]
#set_property -dict {PACKAGE_PIN H14 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_5_P]]
#set_property -dict {PACKAGE_PIN G14 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_5_N]]
#set_property -dict {PACKAGE_PIN E10 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_6_P]]
#set_property -dict {PACKAGE_PIN D10 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_6_N]]
#set_property -dict {PACKAGE_PIN E11 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_7_P]]
#set_property -dict {PACKAGE_PIN D11 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_7_N]]
#set_property -dict {PACKAGE_PIN B12 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_8_P]]
#set_property -dict {PACKAGE_PIN B11 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_8_N]]
#set_property -dict {PACKAGE_PIN F14 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_9_P]]
#set_property -dict {PACKAGE_PIN F13 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_9_N]]
#set_property -dict {PACKAGE_PIN A13 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_10_P]]
#set_property -dict {PACKAGE_PIN A12 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_10_N]]
#set_property -dict {PACKAGE_PIN D9  IOSTANDARD LVCMOS33} [get_ports CRUVI_A_11_P]]
#set_property -dict {PACKAGE_PIN D8  IOSTANDARD LVCMOS33} [get_ports CRUVI_A_11_N]]
#set_property -dict {PACKAGE_PIN G19 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_DI]]
#set_property -dict {PACKAGE_PIN D20 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_DO]]
#set_property -dict {PACKAGE_PIN E20 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_SEL]]
#set_property -dict {PACKAGE_PIN F20 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_MODE]]
#set_property -dict {PACKAGE_PIN G20 IOSTANDARD LVCMOS33} [get_ports CRUVI_A_SCK]]
## }}}
## CRUVI-B
## {{{
#set_property -dict {PACKAGE_PIN G15 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_SMB_ALERT]
#set_property -dict {PACKAGE_PIN F15 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_HSIO]
#set_property -dict {PACKAGE_PIN D15 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_RESET]
#set_property -dict {PACKAGE_PIN G16 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_HSI]
#set_property -dict {PACKAGE_PIN D16 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_HSO]
#set_property -dict {PACKAGE_PIN J16 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_SMB_SDA]
#set_property -dict {PACKAGE_PIN E15 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_SMB_SCL]
#set_property -dict {PACKAGE_PIN E16 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_REFCLK]
#set_property -dict {PACKAGE_PIN A9  IOSTANDARD LVCMOS33} [get_ports CRUVI_B_0_P]
#set_property -dict {PACKAGE_PIN A8  IOSTANDARD LVCMOS33} [get_ports CRUVI_B_0_N]
#set_property -dict {PACKAGE_PIN B10 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_1_P]
#set_property -dict {PACKAGE_PIN A10 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_1_N]
#set_property -dict {PACKAGE_PIN G12 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_2_P]
#set_property -dict {PACKAGE_PIN F12 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_2_N]
#set_property -dict {PACKAGE_PIN E13 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_3_P]
#set_property -dict {PACKAGE_PIN E12 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_3_N]
#set_property -dict {PACKAGE_PIN J13 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_4_P]
#set_property -dict {PACKAGE_PIN H13 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_4_N]
#set_property -dict {PACKAGE_PIN H12 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_5_P]
#set_property -dict {PACKAGE_PIN H11 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_5_N]
#set_property -dict {PACKAGE_PIN G11 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_6_P]
#set_property -dict {PACKAGE_PIN F10 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_6_N]
#set_property -dict {PACKAGE_PIN C12 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_7_P]
#set_property -dict {PACKAGE_PIN C11 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_7_N]
#set_property -dict {PACKAGE_PIN C9  IOSTANDARD LVCMOS33} [get_ports CRUVI_B_8_P]
#set_property -dict {PACKAGE_PIN B9  IOSTANDARD LVCMOS33} [get_ports CRUVI_B_8_N]
#set_property -dict {PACKAGE_PIN J11 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_9_P]
#set_property -dict {PACKAGE_PIN J10 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_9_N]
#set_property -dict {PACKAGE_PIN H9  IOSTANDARD LVCMOS33} [get_ports CRUVI_B_10_P]
#set_property -dict {PACKAGE_PIN H8  IOSTANDARD LVCMOS33} [get_ports CRUVI_B_10_N]
#set_property -dict {PACKAGE_PIN G10 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_11_P]
#set_property -dict {PACKAGE_PIN G9  IOSTANDARD LVCMOS33} [get_ports CRUVI_B_11_N]

#set_property -dict {PACKAGE_PIN J15 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_DI]
#set_property -dict {PACKAGE_PIN C18 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_DO]
#set_property -dict {PACKAGE_PIN E18 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_MODE]
#set_property -dict {PACKAGE_PIN D18 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_SEL]
#set_property -dict {PACKAGE_PIN D19 IOSTANDARD LVCMOS33} [get_ports CRUVI_B_SCK]
##
## We have an eMMC daughter board connected to CRUVI B
#set_property -dict {PACKAGE_PIN D15 IOSTANDARD LVCMOS33} [get_ports o_cruvmmc_hwreset_n]
#set_property -dict {PACKAGE_PIN J16 IOSTANDARD LVCMOS33} [get_ports io_i2c_cruvi_emmc_sda];		## Address 0x52
#set_property -dict {PACKAGE_PIN E15 IOSTANDARD LVCMOS33} [get_ports io_i2c_cruvi_emmc_scl]

#set_property -dict {PACKAGE_PIN B10 IOSTANDARD LVCMOS33} [get_ports io_cruvmmc_cmd];		## B1P
#set_property -dict {PACKAGE_PIN G12 IOSTANDARD LVCMOS33} [get_ports o_cruvmmc_clk];		## B2P
#set_property -dict {PACKAGE_PIN H9  IOSTANDARD LVCMOS33} [get_ports io_cruvmmc_dat[0]];		## B10P
#set_property -dict {PACKAGE_PIN H8  IOSTANDARD LVCMOS33} [get_ports io_cruvmmc_dat[1]];		## B10N
#set_property -dict {PACKAGE_PIN E13 IOSTANDARD LVCMOS33} [get_ports io_cruvmmc_dat[2]];		## B3P
#set_property -dict {PACKAGE_PIN E12 IOSTANDARD LVCMOS33} [get_ports io_cruvmmc_dat[3]];		## B3N
#set_property -dict {PACKAGE_PIN J13 IOSTANDARD LVCMOS33} [get_ports io_cruvmmc_dat[4]];		## B4P
#set_property -dict {PACKAGE_PIN H13 IOSTANDARD LVCMOS33} [get_ports io_cruvmmc_dat[5]];		## B4N
#set_property -dict {PACKAGE_PIN J11 IOSTANDARD LVCMOS33} [get_ports io_cruvmmc_dat[6]];		## B9P
#set_property -dict {PACKAGE_PIN J10 IOSTANDARD LVCMOS33} [get_ports io_cruvmmc_dat[7]];		## B9N
#set_property -dict {PACKAGE_PIN G11 IOSTANDARD LVCMOS33} [get_ports i_cruvmmc_ds];		## B6P
## }}}

## Hard test points
## {{{
#set_property -dict {PACKAGE_PIN M17 IOSTANDARD LVCMOS33} [get_ports o_tp[0]];		## TP8
#set_property -dict {PACKAGE_PIN L18 IOSTANDARD LVCMOS33} [get_ports o_tp[1]];		## TP9
#set_property -dict {PACKAGE_PIN L17 IOSTANDARD LVCMOS33} [get_ports o_tp[2]];		## TP10
#set_property -dict {PACKAGE_PIN K18 IOSTANDARD LVCMOS33} [get_ports o_tp[3]];		## TP11
## }}}

## Bitstream options
set_property CONFIG_MODE SPIx4 [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 26 [current_design]
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CFGBVS GND [current_design];	## Current design has CFGBVS connected to ground
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]

## set_property INTERNAL_VREF 0.750 [get_iobanks 32];	# Rev2 has a proper VREF
## set_property INTERNAL_VREF 0.750 [get_iobanks 33];	# Rev2 has a proper VREF
## set_property INTERNAL_VREF 0.750 [get_iobanks 34];	# Rev2 has a proper VREF
set_property BITSTREAM.CONFIG.UNUSEDPIN PULLNONE [current_design]
set_property BITSTREAM.STARTUP.MATCH_CYCLE 6 [current_design]

