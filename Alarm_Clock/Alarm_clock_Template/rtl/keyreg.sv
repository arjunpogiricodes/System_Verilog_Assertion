/********************************************************************************************

Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
www.maven-silicon.com

All Rights Reserved.

This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd.
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.

Filename		:	keyreg.sv   

Description		:	Key register unit of alarm clock
                                 
Author			:	Prasanna Kulkarni

Support e-mail	:	techsupport_vm@maven-silicon.com 

Version        	:	1.0


*********************************************************************************************/

module keyreg(reset,
              clock,
              shift,
              key,
              key_buffer_ls_min,
              key_buffer_ms_min,
              key_buffer_ls_hr,
              key_buffer_ms_hr);
// Define input and output port direction
  input reset,
        clock,
        shift;
  input [3:0] key;
  output reg [3:0]  key_buffer_ls_min,
                    key_buffer_ms_min,
                    key_buffer_ls_hr,
                    key_buffer_ms_hr;



///////////////////////////////////////////////////////////////////
// This procedure stores the last 4 keys pressed. The FSM block
// detects the new key value and triggers the shift pulse to shift
// in the new key value.
///////////////////////////////////////////////////////////////////
always @(posedge clock or posedge reset)
begin
  // For asynchronous reset, reset the key_buffer output register to 1'b0
  if (reset)
  begin
    key_buffer_ls_min <= 0;
    key_buffer_ms_min <= 0;
    key_buffer_ls_hr <= 0;
    key_buffer_ms_hr <= 0;
  end
  // Else if there is a shift, perform left shift from LS_MIN to MS_HR
  else  if (shift == 1)
  begin
    key_buffer_ms_hr  <= key_buffer_ls_hr;
    key_buffer_ls_hr  <= key_buffer_ms_min;
    key_buffer_ms_min <= key_buffer_ls_min;
    key_buffer_ls_min <= key;
  end

end

endmodule
