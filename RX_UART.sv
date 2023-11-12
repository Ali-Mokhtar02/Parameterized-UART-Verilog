module Receiver_UART(rst_n,clk,tick,Rx,Rx_Dout,Rx_Done,data_error);

parameter NO_OF_BITS=8;
parameter PARITY_ENABLE=0; // 0: No parity bit, 1: Use a parity bit
parameter STOP_BIT=1;  // 2 possible values 0->2bits 1->1bit

input rst_n,clk,tick,Rx; //tick here is the tick from baud_generator
output  Rx_Done;
output reg data_error; // if data_error happens then reciever must be reseted to function properly
output [NO_OF_BITS-1:0] Rx_Dout; //output port holds Data Frame ONLY

reg reg_rx_done;
reg [1+NO_OF_BITS+PARITY_ENABLE+1-1:0] reg_rx_dout ;   // internal signal that hold the received Start,Data,Parity bits if enabled and Stop bit(s)
//first bit should be zero indicating coummincation started and last bit should be 1 indicating communication ended
reg[5:0] ticks_counter; //counter to count number of ticks
reg[3:0] bits_counter;    // counter to count number of bits

//define FSM
parameter IDLE=2'b00;	//counts to halfway of the tick clock to sample the bits halfway to avoid metastability issues aslo samples the start bit
parameter START=2'b01; // recieve Data bits and the parity bit if enabled
parameter STOP=2'b10; // recieve stop bit

reg[1:0] cs,ns;

assign Rx_Dout= (cs==STOP && reg_rx_done)? reg_rx_dout[NO_OF_BITS:1] : 0  ;
assign Rx_Done = (cs==STOP && reg_rx_done)? 1 : 0 ;

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
		ticks_counter<=0;
		bits_counter<=0;
		reg_rx_dout<=0;
		reg_rx_done<=0;
		data_error<=0;
	end
	else begin
		reg_rx_done<=0;
		case(cs)
			IDLE: begin
				if(~Rx && !data_error) begin 
					if(ticks_counter<7) begin  // Sample Start Bit half way to avoid metastability issues
						ticks_counter<=ticks_counter+1;
						ns<=IDLE;
					end
					else begin
						reg_rx_dout[bits_counter]<=Rx;
						// reset the counters for the start state to sample at half the bit.
						bits_counter<=bits_counter+1;
						ticks_counter<=0;
						ns<=START;
					end
				end
				else begin
					ticks_counter<=0;
					bits_counter<=0;
					ns<=IDLE;
				end
			end

			START: begin
				if(ticks_counter<15) begin
					ticks_counter<=ticks_counter+1;
					ns<=START;
				end
				else if( bits_counter < NO_OF_BITS+1) begin
					reg_rx_dout[bits_counter] <= Rx;
					bits_counter <= bits_counter+1;
					ticks_counter <= 0; // reset tick counter to wait before sampling the next bit
					ns<=START;
					// Check if all the Frame bits are sent then check to see if parity bit is enabled or no
					if(bits_counter== (NO_OF_BITS)) begin
					// after finishing the always block the counter incerments
						if(PARITY_ENABLE) begin
							ns <= START;
						end
						else begin
							ns<=STOP;
						end
					end
				end
				else begin // pairty bit if parity enable is high
					if(Rx!= ^reg_rx_dout[8:1]) begin
						data_error<=1;
						ns<=IDLE;
					end 
					else begin
						reg_rx_dout[bits_counter]<= Rx;
						// receiver can use it to check if the data received was corrupted
						bits_counter<=bits_counter+1;
						ticks_counter<=0;
						ns<=STOP;
					end
				end
			end
			STOP: begin
				if(STOP_BIT) begin //one stop bit is sent sample it  half way
					if(ticks_counter<15) begin
						ticks_counter<=ticks_counter +1;
						ns<=STOP;
					end
					else begin
						//sample last bit
						if(ticks_counter==15) begin
							reg_rx_dout[bits_counter]<=Rx;
							reg_rx_done<=1;
							ticks_counter<=ticks_counter+1;
							ns<=STOP;
						end
						// wait remaining half bit before going to idle state
						else if(ticks_counter<23) begin
							ticks_counter<=ticks_counter+1;
							reg_rx_done<=0;
							ns<=STOP;
						end
						else begin
							ticks_counter<=0;  
							bits_counter<=0;
							ns<=IDLE;
						end
					end
				end
				else begin // 2 stop bit are sent sample them half way
					if(ticks_counter<30) begin
						ticks_counter<=ticks_counter +1;
						ns<=STOP;
					end
					else begin
						//sample last bit
						if(ticks_counter==30) begin
							reg_rx_dout[bits_counter]<=Rx;
							reg_rx_done<=1;
							ticks_counter<=ticks_counter+1;
							ns<=STOP;
						end
						else if(ticks_counter<38) begin
							ticks_counter<=ticks_counter+1;
							reg_rx_done<=0;
							ns<=STOP;
						end
						else begin
							ticks_counter<=0;  
							bits_counter<=0;
							ns<=IDLE;
						end
					end
				end
			end
			default: ns<=IDLE;
		endcase
	end
end

`ifdef enable_assertions_RX

always_comb begin
	if(~rst_n)
		Areset_assertion_Rx:assert final(!Rx_Done && Rx_Dout==0);
	else
		DATA_ERROR_ap: assert (data_error!==1);
end

property start_bit_RX;
	@(posedge tick) disable iff(~rst_n || data_error) $fell(Rx) && cs==IDLE |=> !Rx;
endproperty

property stop_bit_RX;
	@(posedge tick) disable iff(~rst_n || data_error) $fell(Rx) && cs==IDLE |=> ##(16*(NO_OF_BITS+PARITY_ENABLE+1)+10) Rx;
endproperty


property parity_bit_RX;
	@(posedge tick) disable iff(~rst_n) $fell(Rx)&& cs==IDLE && PARITY_ENABLE |=> ##(16*(NO_OF_BITS+PARITY_ENABLE)+10) Rx==^reg_rx_dout[NO_OF_BITS:1];
endproperty

property STOPtoIDLE_transition1;
	@(posedge tick) disable iff(~rst_n) cs==STOP && STOP_BIT && ticks_counter==23 |=> ticks_counter==0 && bits_counter==0 &&cs==IDLE;
endproperty

property STOPtoIDLE_transition2;
	@(posedge tick) disable iff(~rst_n) cs==STOP && !STOP_BIT && ticks_counter==38 |=> ticks_counter==0 && bits_counter==0 &&cs==IDLE;
endproperty

property IDLEtoSTART_transition;
	@(posedge tick) disable iff(~rst_n) cs==IDLE && ticks_counter==7 |=> ticks_counter==0 && bits_counter==1 &&cs==START;
endproperty

property STARTtoSTOP_transition1;
	@(posedge tick) disable iff(~rst_n) cs==START && !PARITY_ENABLE && ticks_counter==15 && bits_counter==NO_OF_BITS |=> ticks_counter==0 && bits_counter==9 &&cs==STOP;
endproperty

property STARTtoSTOP_transition2;
	@(posedge tick) disable iff(~rst_n) cs==START && PARITY_ENABLE && ticks_counter==15 && bits_counter==NO_OF_BITS+1 |=> ticks_counter==0 && bits_counter==10 &&cs==STOP;
endproperty

property internal_tick_counter1_RX;
	@(posedge tick) disable iff(~rst_n) cs==STOP && STOP_BIT |-> ticks_counter<24;
endproperty

property internal_tick_counter2_RX;
	@(posedge tick) disable iff(~rst_n) cs==STOP && !STOP_BIT |-> ticks_counter<39;
endproperty



start_bit_RX_ap: assert property(start_bit_RX);
start_bit_RX_cp: cover property(start_bit_RX);

stop_bit_RX_ap: assert property(stop_bit_RX);
stop_bit_RX_cp: cover property(stop_bit_RX);

parity_bit_RX_ap: assert property(parity_bit_RX);
parity_bit_RX_cp: cover property(parity_bit_RX);

STOPtoIDLE_transition1_ap: assert property(STOPtoIDLE_transition1);
STOPtoIDLE_transition1_cp: cover property(STOPtoIDLE_transition1);

STOPtoIDLE_transition2_ap: assert property(STOPtoIDLE_transition2);
STOPtoIDLE_transition2_cp: cover property(STOPtoIDLE_transition2);

IDLEtoSTART_transition_ap: assert property(IDLEtoSTART_transition);
IDLEtoSTART_transition_cp: cover property(IDLEtoSTART_transition);


STARTtoSTOP_transition1_ap: assert property(STARTtoSTOP_transition1);
STARTtoSTOP_transition1_cp: cover property(STARTtoSTOP_transition1);

STARTtoSTOP_transition2_ap: assert property(STARTtoSTOP_transition2);
STARTtoSTOP_transition2_cp: cover property(STARTtoSTOP_transition2);

internal_tick_counter1_RX_ap: assert property(internal_tick_counter1_RX);
internal_tick_counter1_RX_cp: cover property(internal_tick_counter1_RX);

internal_tick_counter2_RX_ap: assert property(internal_tick_counter2_RX);
internal_tick_counter2_RX_cp: cover property(internal_tick_counter2_RX);

`endif

endmodule