vlib work
vlog Baud_Generator.v Tb_tx_rx.v 
vlog +define+enable_assertions_RX -work work RX_UART.sv +cover -covercells
vlog +define+enable_assertions -work work UART_Transmiter.sv +cover -covercells
vsim -voptargs=+acc work.Final_tb
add wave -position insertpoint  \
sim:/Final_tb/rst_n \
sim:/Final_tb/clk \
sim:/Final_tb/tick \
sim:/Final_tb/dout \
sim:/Final_tb/rx_done \
sim:/Final_tb/rx_inst/ticks_counter \
sim:/Final_tb/rx_inst/bits_counter \
sim:/Final_tb/rx_inst/data_error \
sim:/Final_tb/rx_inst/cs \
sim:/Final_tb/rx_inst/ns \
sim:/Final_tb/tx_start \
sim:/Final_tb/tx_din \
sim:/Final_tb/tx_inst/data_sent \
sim:/Final_tb/tx_done \
sim:/Final_tb/tx \
sim:/Final_tb/tx_inst/tick_counter \
sim:/Final_tb/tx_inst/sent_bits_counter \
sim:/Final_tb/tx_inst/cs \
sim:/Final_tb/tx_inst/ns
add wave /Final_tb/tx_inst/Areset_assertion /Final_tb/tx_inst/internal_data_bus_stable_ap /Final_tb/tx_inst/internal_tick_counter1_ap /Final_tb/tx_inst/internal_tick_counter2_ap /Final_tb/tx_inst/parity_bit_ap /Final_tb/tx_inst/start_bit_ap /Final_tb/tx_inst/stop_bit_ap
run -all