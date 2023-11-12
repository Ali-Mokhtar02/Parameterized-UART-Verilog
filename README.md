# Parameterized-UART-Verilog
Parameterized UART TX,RX and BAUD Generator Verilog Codes
This design is based on oversampling method. the samling rate is 16* Baud Rate.
The design Parameters Determine The Number of Data Bits, Baud Rate, Usage of Parity Bit and Number of Stop Bits.
The Design is guarded by assertions in macros "enable_assertions" and "enable_assertions_RX". A simple testbench is used to 
