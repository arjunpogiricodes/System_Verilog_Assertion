
module fifo_assertions (clk,
						rst_n,
						rd_n,
						wr_n,
						over_flow,
						under_flow );

	input logic rst_n,clk,rd_n,wr_n;
	input logic under_flow,over_flow;

	// RESET - On reset overflow and underflow should be zero 
	
           sequence RES;
                (!rst_n) ;
           endsequence
           
            property reset_prty;
                 @(posedge clk) RES |=> ((!under_flow) &&  (!over_flow ));
             endproperty
	  //FIFO OVERFLOW - After reset if only write is enabled continuously for 
	  //17 times overflow should go high 
	   property overflow_prty;
                  @(posedge clk)  disable iff(!rst_n) (!rst_n)##1(rst_n) ##1 (!wr_n && rd_n)[*17] |=> over_flow ; 
           endproperty
		//FIFO UNDERFLOW - After fifo overflow if only is read is enabled continuously 
	//17 times underflow should go high
	
	   property  underflow_prty;
                  @(posedge clk)  disable iff(!rst_n) (over_flow) ##1 (wr_n && !rd_n)[*17] |=> under_flow ;
           endproperty

	RESET : assert property (reset_prty);
	OVERFLOW:assert property (overflow_prty);
	UNDERFLOW:assert property(underflow_prty);

endmodule
