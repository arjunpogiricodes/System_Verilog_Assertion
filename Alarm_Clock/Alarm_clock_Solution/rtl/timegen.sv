/********************************************************************************************

Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
www.maven-silicon.com

All Rights Reserved.

This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd.
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.

Filename		:	timegen.sv   

Description		:	Time generation unit of alarm clock            
          
Author			:	Prasanna Kulkarni

Support e-mail	:	techsupport_vm@maven-silicon.com 

Version        	:	1.0

*********************************************************************************************/
`timescale 1ns/1ns

module timegen(clock,
               reset,
               reset_count,
               fastwatch,
               one_second,
               one_minute
               );
// Define input and output port directions        
	input clock,
		reset,
		reset_count, //Resets the timegen whenever a new current time is set
		fastwatch;  

	output one_second,
        one_minute;
// Define internal registers required
	reg [13:0] count;
	reg one_second;
	reg one_minute_reg;
	reg one_minute;
 

//One minute pulse generation
always@(posedge clock or posedge reset)
	begin
	// Upon reset, set the one_minute_reg value to zero
		if (reset)
			begin
				count<=14'b0;
				one_minute_reg<=0;
			end
	// Else check if there is a reset from alarm controller and reset the one_minute_reg and count value
		else if (reset_count)
			begin
				count<=14'b0;
				one_minute_reg<=1'b0;
			end
	// Else check if the count value reaches 'd15359 to generate 1 minute pulse
		else if (count[13:0]== 14'd15359)
			begin
				count<=14'b0;
				one_minute_reg<=1'b1;      
			end
	// Else for every posedge of clock just increment the count. 
			else   
				begin
					count<=count+1'b1;
					one_minute_reg<=1'b0;
				end
	end
                             
//One second pulse generation
always@(posedge clock or posedge reset)
	begin
	// If reset is asserted, set one_second and counter_sec value to zero
		if (reset)
			begin
				one_second<=1'b0;
			end
	// Else check if there is reset from alarm_controller, and reset the one_second and counter_sec value    
		else if (reset_count)
			begin
				one_second<=1'b0;
			end
	// Else check if the count value reaches the 'd255 to generate and count 1 sec pulse        
		else if (count[7:0]==8'd255)
			begin
				one_second<=1'b1;
			end
	// Else set the one_second and counter_sec value to zero
			else     
				begin
					one_second<=1'b0;
				end
	end

//Fastwatch Mode Logic that makes the counting faster

always@(*)
	begin
    // If fastwatch is asserted, make one_second equivalent to one_minute
		if(fastwatch)
			one_minute = one_second;
    // Else assert one_minute signal when one_minute_reg is asserted
		else
			one_minute = one_minute_reg; 
	end

wire #1 rst_delay = reset;

//RESET_CHECK - On reset, the signals count, one_second and one_minute should be Zero
	property TG_reset_check;
		@(posedge rst_delay)
			((count == 0) && (one_second == 0) && (one_minute == 0));
	endproperty 

//ONE_SECOND_CHECK - If reset_count is 0 and count is 255 then one_second pulse should be High
	property one_sec_check;
		@(posedge clock) disable iff(reset)
			((~reset_count) && (count == 8'd255)) |=> (one_second == 1'b1);
	endproperty
					
//ONE_MINUTE_CHECK - If reset_count is 0 and count is 15359 then one_minute pulse should be High
	property one_minute_check;
		@(posedge clock) disable iff(reset)
			((~reset_count) && (count == 14'd15359)) |=> (one_minute == 1'b1);
	endproperty

//MINUTE_COUNT_CHECK - If reset_count is 0 and if count is not equal to 15359 then count should increment by 1
	property minute_count_check;
		@(posedge clock) disable iff(reset)
			((~reset_count) && (count[13:0] != 14'd15359)) |=> (count == ($past(count,1) + 1'b1));
	endproperty

//FAST_WATCH_CHECK - if fastwatch is high, one_minute should be equal to one_second
	property fastwatch_check;
		@(posedge clock) disable iff (reset)
			$rose(fastwatch) |-> (one_minute == one_second);
	endproperty


TG_RESET_CHECK     : assert property (TG_reset_check);
ONE_SEC_CHECK 	   : assert property (one_sec_check);
ONE_MINUTE_CHECK   : assert property (one_minute_check);
MINUTE_COUNT_CHECK : assert property (minute_count_check);
FASTWATCH_CHECK    : assert property (fastwatch_check);

endmodule 
