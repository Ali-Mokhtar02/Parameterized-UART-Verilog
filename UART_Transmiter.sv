module TX_UART(rst_n,clk,tx_start,tick,tx_din,tx,tx_done);
parameter NO_OF_BITS=8;
parameter PARITY_ENABLE=0; // 0: No parity bit, 1: Use a parity bit
parameter STOP_BIT=1;  // 2 possible values 0->2bits 1->1bit

input rst_n,clk;
input tx_start,tick; //tx_start must be  high at tick posedge for correct operation
input [NO_OF_BITS-1:0] tx_din;
output reg tx;
output tx_done;

reg reg_tx_done;  //internal tx_done signal
reg[5:0] tick_counter; //internal counters to track sent bits and number of ticks
reg[3:0] sent_bits_counter; 
reg [NO_OF_BITS-1:0] data_sent; // internal signal to hold data to be sent

parameter IDLE=2'b00;
parameter START=2'b01; // start sending start bit
parameter DATA=2'b10; // send data bits and the parity bit if enabled
parameter STOP=2'b11; // send stop bit

reg[1:0] cs,ns;

//output assignment
assign tx_done= (cs===STOP && reg_tx_done===1)? 1: 0;

always @(posedge clk or negedge rst_n) begin
	if (~rst_n) begin
		cs<=IDLE;
	end
	else begin
		cs<=ns;
	end
end

always @(posedge tick or negedge rst_n) begin
	if(~rst_n) begin
		ns<=IDLE;
		tick_counter<=0;
		sent_bits_counter<=0;
		tx<=1; 
		reg_tx_done<=0;
		data_sent<=0;
	end
	else begin
		case(cs)
			IDLE: begin
				reg_tx_done<=0;
				tx<=1;
				if(tx_start) begin
					data_sent<=tx_din;
					tx<=0; //start communication 
					ns<=START;
				end		
				else
					ns<=IDLE;
			end
			START: begin //send start bit
				tx<=0;
				if(tick_counter<15) begin
					tick_counter<=tick_counter+1;
					ns<=START;
				end
				else begin
					tick_counter<=0;
					tx<=data_sent[sent_bits_counter]; //tx takes value of LSB of din
					ns<=DATA;
				end
			end
			DATA: begin //send data bits + parity bit
				if(tick_counter<15) begin
					tick_counter<=tick_counter+1;
					ns<=DATA;
				end
				else if(sent_bits_counter< NO_OF_BITS) begin
						tx<=data_sent[sent_bits_counter+1]; // tx takes next bit value
						tick_counter<=0;
						sent_bits_counter<=sent_bits_counter+1;
						ns<=DATA;
					// after sending all data bits check if parity bit is enabled
					if(sent_bits_counter== (NO_OF_BITS -1)) begin
						if(PARITY_ENABLE) begin
							tx<= ^data_sent[NO_OF_BITS-1:0];
							ns<= DATA;
						end
						else begin
							tx<=1; //stop bit
							tick_counter<=0;
							ns<=STOP;
						end
						//bits counter increments after finising the always block
					end
				end
				else begin
					//parity bit is sent 
					tx<=1; //send stop bit
					tick_counter<=0; 
					ns<=STOP;
				end
			end
			STOP: begin
				tx=1;
				if(STOP_BIT) begin
					if(tick_counter<15) begin
						tick_counter<=tick_counter +1;
						ns<=STOP;
					end
					else begin
						//reset tick and bit counters for next operation
						tick_counter<=0;  
						sent_bits_counter<=0;
						reg_tx_done<=1;
						ns<=IDLE;
					end
				end
				else begin // 2 stop bits
					if(tick_counter<30) begin
						tick_counter<=tick_counter +1;
						ns<=STOP;
					end
					else begin
						tick_counter<=0;
						sent_bits_counter<=0;
						reg_tx_done<=1;
						ns<=IDLE;
					end
				end
			end
			default: ns<=IDLE;
		endcase
	end
end

`ifdef enable_assertions
always_comb begin
	if(~rst_n)
		Areset_assertion:assert final(!tx_done);
end

property start_bit;
	@(posedge tick) disable iff(~rst_n) $rose(tx_start) && cs==IDLE |=> !tx;
endproperty

property stop_bit;
	@(posedge tick) disable iff(~rst_n) $rose(tx_start) && cs==IDLE |=> ##(16*(NO_OF_BITS+PARITY_ENABLE+1)) tx;
endproperty


property parity_bit;
	@(posedge tick) disable iff(~rst_n) $rose(tx_start)&& cs==IDLE && PARITY_ENABLE |=> ##(16*(NO_OF_BITS+PARITY_ENABLE)) tx==^data_sent[NO_OF_BITS-1:0];
endproperty

property internal_data_bus_stable;
	@(posedge tick) disable iff(~rst_n) cs!=IDLE |=> $stable(data_sent);
endproperty

property internal_tick_counter1;
	@(posedge tick) disable iff(~rst_n) cs==STOP && STOP_BIT |-> tick_counter<16;
endproperty

property internal_tick_counter2;
	@(posedge tick) disable iff(~rst_n) cs==STOP && !STOP_BIT |-> tick_counter<31;
endproperty



start_bit_ap: assert property(start_bit);
start_bit_cp: cover property(start_bit);

stop_bit_ap: assert property(stop_bit);
stop_bit_cp: cover property(stop_bit);

parity_bit_ap: assert property(parity_bit);
parity_bit_cp: cover property(parity_bit);

internal_data_bus_stable_ap: assert property(internal_data_bus_stable);
internal_data_bus_stable_cp: cover property(internal_data_bus_stable);

internal_tick_counter1_ap: assert property(internal_tick_counter1);
internal_tick_counter1_cp: cover property(internal_tick_counter1);

internal_tick_counter2_ap: assert property(internal_tick_counter2);
internal_tick_counter2_cp: cover property(internal_tick_counter2);

`endif
endmodule

