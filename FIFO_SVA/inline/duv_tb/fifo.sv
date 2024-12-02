


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
									over_flow <= 1'b1;
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
					read_ptr <= `PTR_SIZE'b0; //Error in DUT - RESET assertion will fail 
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
								write_ptr <=  write_ptr + 1'b1; // Error - ASSERTION - WRITE will catch this bug
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
		
		
	// RESET
	sequence reset_seq;
		( (!read_ptr) && (!write_ptr) && (!fifo_status) && (!under_flow) && (!over_flow) );
	endsequence

	property reset_prty;
		@(posedge clk) (~rst_n) |-> reset_seq; 
	endproperty

	// FIFO FULL - Iffifo_status is 15 & fifo is not full,
	//and write signal is enabled next cycle full will go high
	
        sequence fifo_full_sta;
                  (fifo_status == 15) && (!full) && (!wr_n);
        endsequence

        property full_prty;
               @(posedge clk) fifo_full_sta |=>  full;
        endproperty  
               
                   

	// FIFO EMPTY - If fifo_status is 0 & fifo is not empty,
	//and read signal is enabled next cycle full will go high
	
	 sequence fifo_full_emsta;
            (fifo_status == 0) && (!empty) && (!rd_n);            
         endsequence

         property empty_prty;
            @(posedge clk)  fifo_full_emsta  |=> empty;  
         endproperty

	//FIFO UNDERFLOW - If fifo is empty and only read signal is enabled 
    // next cycle underflow will go high	
	 sequence under;
           (empty) && (!rd_n);         
         endsequence
	 property underflow_prty;
           @(posedge clk) under |=> under_flow ;
         endproperty
	
	//FIFO OVERFLOW - If fifo is full and only write signal is enabled 
    // next cycle overflow will go high
	
	 sequence over;
            (full) && (!wr_n);
         endsequence  

         property overflow_prty;
            @(posedge clk) over |=> over_flow ;
         endproperty
	

	//Read pointer reset - If read signal is enabled and read pointer is 15
	//next cycle the write pointer resets back to 0 
	  
         sequence read_p;
           (!rd_n) && (read_ptr == 15) && (!empty) ;  
         endsequence  
	
        property rp_rst_prty;
            @(posedge clk) read_p |=> read_ptr <= 0;
        endproperty
	
	// Write pointer reset - If write signal is enabled and write pointer is 15
	//next cycle the write pointer resets back to 0 
	
         sequence write_p;
             (!wr_n) &&  (write_ptr == 15) ;
         endsequence  
        
         property wr_rst_prty;
              @(posedge clk) write_p |=> write_ptr <= 0;
         endproperty
	
	// Continuous Writing - If write pointer is zero & if continuous write operation is done for sixteen times 
	//without read operation, next cycle the write pointer should go back to zero
	
	  sequence con_write;
               ((write_ptr == 0) && (!wr_n) && (rd_n) ) ##1 ((!wr_n) && write_ptr [*15] ) ;
          endsequence 

          property write_prty;
                @(posedge clk)  con_write |=>  write_ptr <=0;
          endproperty  
	//Continuous Reading - If read pointer is zero & if continuous read operation is done for sixteen times
	//without write operation, next cycle the write pointer should go back to zero
	
	 sequence con_read;
                 (( read_ptr == 0) && (wr_n) && (!rd_n)) ##1 ((!rd_n) && read_ptr [*15] )  ;
         endsequence

          property read_prty;
                     @(posedge clk)  con_read |=>  read_ptr <=0;
          endproperty
	

	//Fifo status increment - If fifo status is not equal to 15, full is 0 ,
	//and only write signal is enabled next cycle fifo status will increment
	
	  sequence w_status;
                (fifo_status != 15 ) &&  (!full) && (!wr_n) && (rd_n)  ;
          endsequence 

          property wcnt_prty;
                @(posedge clk)   w_status |=>  (fifo_status == ($past(fifo_status) + 1));
          endproperty
	
	//Fifo status decrement - If fifo status is not equal to 0, empty is 0 ,
	//and only read signal is enabled next cycle fifo status will decrement
	    sequence r_status;
                  (fifo_status != 0 ) &&  (!empty) && (wr_n) && (!rd_n) ;
            endsequence

            property rcnt_prty;
                    @(posedge clk)  r_status |=> (fifo_status == ($past(fifo_status) - 1));

            endproperty 
	
	
	
	//Write pointer increment - After every write operation write pointer should increment
    //Take care of full condition
	
	 sequence w_ptr_inc;
                  (!wr_n) && (!full);
           endsequence

          property wr_pointer;
                   @(posedge clk)   w_ptr_inc |=>  ( write_ptr == ($past( write_ptr) + 1));
          endproperty
	
	// Read pointer increment - After every read operation read pointer should increment
    //Take care of full condition
	
	  sequence r_ptr_inc;
                      (!rd_n) && (!empty) ;             
          endsequence

          property rd_pointer;
                     @(posedge clk)   r_ptr_inc |->  ( read_ptr == ($past( read_ptr ) + 1));

           endproperty  

	RESET : assert property (reset_prty);
	FIFO_FULL : assert property (full_prty);
	FIFO_EMPTY : assert property (empty_prty);
	UNDERFLOW : assert property (underflow_prty);
	OVERFLOW : assert property (overflow_prty);
	FIFO_RP_RST : assert property (rp_rst_prty);
	FIFO_WR_RST :  assert property (wr_rst_prty);
	WRITE : assert property (write_prty);
	READ : cover property (read_prty);
	STATUS_WCNT : cover property (wcnt_prty);
	STATUS_RCNT : cover property (rcnt_prty);
	RD_PTR : assert property(rd_pointer);
	WR_PTR : assert property(wr_pointer);
endmodule


  

  
  


  
  
  
















