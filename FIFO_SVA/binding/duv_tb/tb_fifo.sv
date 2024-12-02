/********************************************************************************************

Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
www.maven-silicon.com

All Rights Reserved.

This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd.
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.


Filename		:	tb_fifo.sv   

Description		:	FIFO TB

Author Name		:	Putta Satish

Support e-mail  : 	For any queries, reach out to us on "tech_support@maven-silicon.com" 

Version			:	1.0

*********************************************************************************************/


module tb_fifo();

	reg clk; 
	reg rst_n;
	reg rd_n; 
	reg wr_n;
	reg [7:0] data_in;

	wire [7:0] data_out;
	wire under_flow, over_flow;

	fifo  DUV  (.clk(clk),
				.data_in(data_in),
				.rd_n(rd_n),
				.rst_n(rst_n),
				.wr_n(wr_n),
				.data_out(data_out),
				.over_flow(over_flow),
				.under_flow(under_flow) );
	// Instantiate the assertion module and connect to DUT module using bind keyword
       bind DUV fifo_assertions  ASSERT(.clk(clk),.rst_n(rst_n),.rd_n(rd_n),.wr_n(wr_n),.over_flow(over_flow),.under_flow(under_flow));
	
	
	//Clock generation
	always
		begin
			#5 clk = 1'b0;
			#5 clk = 1'b1;
		end

	//Reset the FIFO
	task reset_fifo;
		begin
			rst_n <= 1'b0;
			data_in <= $random;
			rd_n <= 1'b1;
			wr_n <= 1'b1;
			repeat(3)
				@(negedge clk);
			rst_n <= 1'b1;
		end
	endtask

	//Write / Read
	task wr_rd (input [15:0] wr_data, input wr, input rd);
		begin
			data_in = wr_data;
			rd_n = rd;
			wr_n = wr;
			if(~wr_n)
				$display("FIFO WRITE: Data = %d  \n", data_in);
			@(posedge clk);
			@(negedge clk);
			if(~rd_n)
				$display("FIFO READ:  Data = %d \n", data_out);
		end
	endtask

	initial
		begin: STIM
			integer i;
			reset_fifo;
			//Writing Data into all the locations
			$display("\n\n ************ WRITING INTO FIFO ************* \n\n ");
			for(i=16; i>0; i=i-1)
				begin
					wr_rd(i,1'b0,1'b1);
				end

			//Writing when FIFO is full
			wr_rd(8'b1,1'b0,1'b1);
			wr_rd(8'b1,1'b0,1'b1);


			//Reading Data 
			$display("\n\n ************ READING FIFO ************* \n\n ");
			repeat(16)
				begin
					wr_rd(8'd0,1'b1,1'b0);
				end

			//Reading when FIFO is empty
			wr_rd(8'b0,1'b1,1'b0);
			wr_rd(8'b0,1'b1,1'b0);

			//Write then Read
			//Write
			wr_rd(8'd0,1'b0,1'b1);
			wr_rd(8'd1,1'b0,1'b1);
			//Read
			wr_rd(8'd0,1'b1,1'b0);
			wr_rd(8'd0,1'b1,1'b0);

			//Write and Read
			wr_rd(8'd2,1'b0,1'b1);
			wr_rd(8'd3,1'b0,1'b1);
			//Simultaneous Read & Write
			wr_rd(8'd8,1'b0,1'b0);

			$finish;

		end

	initial
		begin

		`ifdef VCS
                $fsdbDumpSVA(0,tb_fifo);
                $fsdbDumpvars(0, tb_fifo);
                `endif	
	
		$monitor("********* FIFO : Underflow = %b, Overflow = %b **********",under_flow,over_flow);
		end

endmodule

