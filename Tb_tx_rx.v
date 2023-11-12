module Final_tb();
reg rst_n,clk;
wire tick;
reg tx_start;
reg[7:0] tx_din;
wire [7:0] dout;
wire rx_done,tx,tx_done;
wire data_error;

Baud_Gen baud_inst(clk,rst_n,tick);
Receiver_UART rx_inst(rst_n,clk,tick,tx,dout,rx_done,data_error);
TX_UART tx_inst(rst_n, clk, tx_start, tick, tx_din, tx, tx_done);

initial begin
	clk=0;
	forever
		#1 clk=~clk;
end

initial begin
	repeat(5) begin
		rst_n=0;
		tx_start=$random;
		tx_din=$random;
		@(negedge clk);
		rst_n=1;
		tx_start=1;
		@(negedge tick)
		//start transmiting
		//garbage values it shouldn't affect the opertaion
		repeat(16*(1+8+1+2)+10) begin
			@(negedge tick);
			tx_start=$random;
			tx_din=$random;
		end
	end
	rst_n=0;
	@(negedge clk);
	@(negedge clk);
	$stop;
end
endmodule