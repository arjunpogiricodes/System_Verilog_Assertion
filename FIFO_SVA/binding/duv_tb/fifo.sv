
`define FIFO_DEPTH 16	// FIFO depth
`define DATA_WIDTH 8    // Data bus width
`define PTR_SIZE 4 	// Read and Write pointers size 

module fifo (clk,
			 rst_n,
             rd_n,
			 wr_n,
			 data_in,
             data_out,
			 over_flow,
			 under_flow );

	input clk;
	input rst_n;
	input rd_n; 
	input wr_n;

	// Input data bus
	input [`DATA_WIDTH-1:0] data_in;

	//Output data bus
	output [`DATA_WIDTH-1:0] data_out;

	//FLAGS - indiacte the FIFO status
	output under_flow, over_flow;

	reg under_flow, over_flow;

	reg full,empty;

	reg [`DATA_WIDTH-1:0] data_out;

	//FIFO Memory
	reg [`DATA_WIDTH-1:0] fifo_mem [0:`FIFO_DEPTH-1];

	//fifo_status to track the FIFO status 							
	reg [`PTR_SIZE-1:0] fifo_status;
							
	reg [`PTR_SIZE-1:0] read_ptr;  //Read from next location
	reg [`PTR_SIZE-1:0] write_ptr; //Write into next location

	//Reading and Writing of FIFO
	always @ (posedge clk or negedge rst_n)
		begin
			if(~rst_n)
				begin
					under_flow <= 1'b0;
					over_flow <= 1'b0;
				end //if
			else
				begin      
					if(~rd_n)
						begin
							if(!empty)
								begin
									data_out <= fifo_mem[read_ptr];
									under_flow <= 1'b0;
								end
							else
								begin
									$display("READ ERROR: FIFO IS EMPTY \n");
									under_flow <= 1'b1;
								end
						end //if
					else
						under_flow <= 1'b0;
    
					if(~wr_n)
						begin
							if(!full)
								begin
									fifo_mem[write_ptr] <= data_in;
									over_flow <= 1'b0;
								end
							else
								begin
									$display("WRITE ERROR: FIFO IS FULL \n");
									over_flow <= 1'b0;
								end
						end //if
					else
						over_flow <= 1'b0;
				end //else 
		end
  
	//Read Pointer and Write Pointer
	always @ (posedge clk or negedge rst_n)
		begin
			if(~rst_n)
				begin
					//read_ptr <= `PTR_SIZE'b0;
					read_ptr <= `PTR_SIZE'b1; //Error in DUT - RESET assertion will fail 
					write_ptr <= `PTR_SIZE'b0;	
				end
			else
				begin
					if(~rd_n && ~empty)
						begin
							if (read_ptr == `FIFO_DEPTH-1)
								read_ptr <= `PTR_SIZE'b0;
							else
								read_ptr <=  read_ptr + 1'b1;
						end
					if(~wr_n && ~full)
						begin
							if (write_ptr == `FIFO_DEPTH-1)
								write_ptr <= `PTR_SIZE'b0;
							else
								//write_ptr <=  write_ptr + 1'b1; 
								write_ptr <=  write_ptr + 1'b0; // Error - ASSERTION - WRITE will catch this bug
						end 
				end
		end
	
  
	//Tracking the FIFO status
	always @ (posedge clk or negedge rst_n)
		begin
			if(~rst_n)              
				fifo_status <= `PTR_SIZE'b0;
			else if((fifo_status==`FIFO_DEPTH-1) && (~wr_n))
				fifo_status<=`FIFO_DEPTH-1;
			else if((fifo_status==`PTR_SIZE'b0) && (~rd_n))
				fifo_status<=`PTR_SIZE'b0;
			else if(rd_n==1'b0 && wr_n==1'b1 && empty==1'b0)      
				fifo_status <= fifo_status - 1'b1;
			else if(wr_n==1'b0 && rd_n==1'b1 && full==1'b0)     
				fifo_status <= fifo_status + 1'b1;       
		end 
  
	//Generating the flags from FIFO status - FULL or EMPTY 
	always @ (posedge clk or negedge rst_n)
		begin
			if(~rst_n)
				begin
					full <= 1'b0;
					empty <= 1'b1;
				end
			else
				begin
					if(fifo_status == `FIFO_DEPTH-1)
						full <= 1'b1;
					else
						full <= 1'b0;

					if(fifo_status == `PTR_SIZE'b0 )
						empty <= 1'b1;
					else
						empty <= 1'b0;
				end
		end

endmodule


   


