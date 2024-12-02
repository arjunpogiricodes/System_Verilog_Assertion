/********************************************************************************************

Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
www.maven-silicon.com

All Rights Reserved.

This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd.
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.

Filename		:	counter.sv   

Description		:	Counter unit of alarm clock

Author			:	Prasanna Kulkarni

Support e-mail 	:	techsupport_vm@maven-silicon.com 

Version        	: 	1.0

*********************************************************************************************/
`timescale 1ns/1ns

module counter (clk,
				reset,
				one_minute,
				load_new_c,
				new_current_time_ms_hr,
				new_current_time_ms_min,
				new_current_time_ls_hr,
				new_current_time_ls_min,
				current_time_ms_hr,
				current_time_ms_min,
				current_time_ls_hr,
				current_time_ls_min);
				
// Define input and output port directions
	input clk,
		reset,
		one_minute,
		load_new_c;

	input[3:0] new_current_time_ms_hr,
			new_current_time_ms_min,
			new_current_time_ls_hr,
			new_current_time_ls_min;

	output [3:0] current_time_ms_hr,
            current_time_ms_min,
            current_time_ls_hr,
            current_time_ls_min;
			
// Define register to store current time
	reg [3:0] current_time_ms_hr,
			current_time_ms_min,
			current_time_ls_hr,
			current_time_ls_min;

// Lodable Binary up synchronous Counter logic  /******************************

// Write an always block with asynchronous reset 
always@( posedge clk or posedge reset)                                         
	begin              
// Check for reset signal and upon reset load the current_time register with default value (1'b0)                                                                                                       
		if(reset)                                                                 
			begin
				current_time_ms_hr  <= 4'd0;                                          
				current_time_ms_min <= 4'd0;                                          
				current_time_ls_hr  <= 4'd0;
				current_time_ls_min <= 4'd0;
			end
// Else if there is no reset, then check for load_new_c signal and load new_current_time to current_time register
		else if(load_new_c)
			begin                                                                
				current_time_ms_hr  <= new_current_time_ms_hr;                     //   Corner cases: ms_hr ls_hr :ms_min ls_min
				current_time_ms_min <= new_current_time_ms_min;                    //              2       3       5       9  -> 00:00
				current_time_ls_hr  <= new_current_time_ls_hr;                     //              0       9       5       9  -> 10:00
				current_time_ls_min <= new_current_time_ls_min;                    //              0       0       5       9  -> 01:00
			end                                                                    //              0       0       0       9  -> 00:10
// Else if there is no load_new_c signal, then check for one_minute signal and implement the counting algorithm
		else if (one_minute == 1)
			begin
    // Check for the corner case
    // If the current_time is 23:59, then the next current_time will be 00:00
				if(current_time_ms_hr == 4'd2 && current_time_ms_min == 4'd5 &&
					current_time_ls_hr == 4'd3 && current_time_ls_min == 4'd9)
					begin
						current_time_ms_hr  <= 4'd0;
						current_time_ms_min <= 4'd0;
						current_time_ls_hr  <= 4'd0;
						current_time_ls_min <= 4'd0;
					end
    // Else check if the current_time is 09:59, then the next current_time will be 10:00
				else if(current_time_ls_hr == 4'd9 && current_time_ms_min == 4'd5
					&& current_time_ls_min == 4'd9)
					begin
						current_time_ms_hr <= current_time_ms_hr + 1'd1;
						current_time_ls_hr <= 4'd0;
						current_time_ms_min <= 4'd0;
						current_time_ls_min <= 4'd0;
					end
    // Else check if the time represented by minutes is 59, Increment the LS_HR by 1 and set MS_MIN and LS_MIN to 1'b0
				else if (current_time_ms_min == 4'd5 && current_time_ls_min == 4'd9)
					begin
						current_time_ls_hr <= current_time_ls_hr + 1'd1;
						current_time_ms_min <= 4'd0;
						current_time_ls_min <= 4'd0;
					end
    // Else check if the LS_MIN is equal to 9, Increment the MS_MIN by 1 and set MS_MIN to 1'b0
				else if(current_time_ls_min == 4'd9)
					begin
						current_time_ms_min <= current_time_ms_min + 1'd1;
						current_time_ls_min <= 4'd0;
					end
    // Else just increment the LS_MIN by 1
				else 
					begin
						current_time_ls_min <= current_time_ls_min + 1'b1;
					end
			
			end
    end

	wire #1 rst_delay = reset;

//RESET_CHECK - On reset, the signals current_time_ms_hr,current_time_ls_hr,current_time_ms_min,current_time_ls_min should be zero
	// Sequence to check current time as 00:00
	sequence reset_seq; 
		((current_time_ms_hr  == 4'd0) && (current_time_ms_min == 4'd0) && (current_time_ls_hr  == 4'd0) && (current_time_ls_min == 4'd0));
	endsequence

	property reset_check;
		@(posedge rst_delay)  reset_seq;
	endproperty

//TIMER_WRAP_BACK_CHECK - If one_minute is high and current time is 23:59 then current time should be immediately zero
	//sequence to check one minute pulse and current time as 23:59
	sequence hour_seq1;
		((one_minute) && (current_time_ms_hr == 4'd2) && (current_time_ms_min == 4'd5) && (current_time_ls_hr == 4'd3) && (current_time_ls_min == 4'd9));
	endsequence

	//sequence to check current time as 00:00
	sequence hour_seq2;
		((current_time_ms_hr  == 4'd0) && (current_time_ms_min == 4'd0) && (current_time_ls_hr  == 4'd0) && (current_time_ls_min == 4'd0));
	endsequence

	property timer_wrap_back;
		@(posedge clk) disable iff(reset)
			hour_seq1 |=> hour_seq2;
	endproperty

//LOAD_NEW_CURRENT_TIME_CHECK - If load_new_c is high, then new_current_time and current_time should be same
	//sequence to check new_currrent_time and current_time
	sequence hour_seq3;
		((current_time_ms_hr  == new_current_time_ms_hr) && (current_time_ms_min == new_current_time_ms_min) &&	(current_time_ls_hr  == new_current_time_ls_hr) && (current_time_ls_min == new_current_time_ls_min));
	endsequence

	property load_new_current_time;
		@(posedge clk) disable iff(reset)
			(load_new_c) |=> hour_seq3;
	endproperty

//LS_HR_WRAP_BACK_CHECK - If one_minute is high and current time is 9:59, then current_time_ms_hr should be incremented by 1 and ls_hr, ms_min and ls_min as zero
	//sequence to check one minute pulse and current time as 9:59
	sequence hour_seq5;
		((one_minute) && (current_time_ms_min == 4'd5) && (current_time_ls_hr == 4'd9) && (current_time_ls_min == 4'd9));
	endsequence

	//sequence to check current time ms_hr increment by 1 and ls_hr, ms_min and ls_min as zero
	sequence hour_seq6;
		((current_time_ms_hr  ==  $past(current_time_ms_hr, 1) + 1'b1) && (current_time_ms_min == 4'd0) && (current_time_ls_hr  == 4'd0) && (current_time_ls_min == 4'd0));
	endsequence

	property ls_hr_wrap_back;
		@(posedge clk) disable iff(reset)
			hour_seq5 |=> hour_seq6;
	endproperty

//MIN_WRAP_BACK_CHECK - If one_minute is high and if current time is 00:59 then, both current time ms_min and ls_min should be zero
	//sequence to check one minute pulse and in current time is 00:59
	sequence min_seq1;
		((one_minute) && (current_time_ms_min == 4'd5) && (current_time_ls_min == 4'd9));
	endsequence

	//sequence to check current time ms_min and ls_min should be zero
	sequence min_seq2;
		((current_time_ms_min  == 4'd0) && (current_time_ls_min == 4'd0));
	endsequence

	property min_wrap_back;
		@(posedge clk) disable iff(reset)
			min_seq1 |=> min_seq2;
	endproperty


//LS_MIN_INCR_CHECK  - If one_minute is high and if current_time_ls_min is less than 9, then current_time_ls_min should increment by 1
	//sequence to check one minute pulse and current time_ls_min less than 9
	sequence min_seq4;
		((one_minute) && (current_time_ls_min < 4'd9));
	endsequence

	property minute_incr_check;
		@(posedge clk) disable iff(reset)
			min_seq4 |=> (current_time_ls_min  ==  $past(current_time_ls_min, 1) + 1'b1);
	endproperty


COUNTER_RESET_CHECK	    	: assert property (reset_check);
TIMER_WRAP_BACK_CHECK       : assert property (timer_wrap_back);
LOAD_NEW_CURRENT_TIME_CHECK : assert property (load_new_current_time);
LS_HR_WRAP_BACK_CHECK	    : assert property (ls_hr_wrap_back);
MIN_WRAP_BACK_CHECK         : assert property (min_wrap_back);
LS_MIN_INCR_CHECK           : assert property (minute_incr_check);

endmodule

