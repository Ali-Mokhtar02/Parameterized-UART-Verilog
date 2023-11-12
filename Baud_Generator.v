// generates a clock 16 time faster than the given BAUDRATE for oversamlping
module Baud_Gen(clk,rst_n,tick);
input rst_n,clk;
output reg tick;

parameter CLK_SPEED= 'd100_000000; //default is 100MHz
parameter BAUD_RATE= 'd9600;  // default is 9600 bits per second
parameter Clocks_Per_Bit= CLK_SPEED/(16* BAUD_RATE); // calculate number of clocks needed to send one bit

reg [11:0] counter; // counter to send tick when it reaches Clocks_Per_Bit

always @(posedge clk or negedge rst_n) begin
	if (~rst_n) begin
	tick=0;
	counter=1;		
	end
	else if (counter<Clocks_Per_Bit) begin
		counter=counter+1;	
		tick=0;
	end
	else begin
		tick=1;
		counter=1;
	end
end

endmodule