


`timescale 1ns/1ns

module fsm_assertions ( clock, 
						reset, 
						one_second,
						time_button, 
						alarm_button,
						key,
						load_new_a,
						show_a,
						show_new_time,
						load_new_c,
						shift,
						reset_count);
	input clock,reset,one_second,time_button,alarm_button;
	input [3:0] key;
	input load_new_a,show_a,show_new_time,load_new_c,shift,	reset_count;
	
	wire #1 rst_delay = reset;	   
	
//RESET CHECK - On reset the present state should be in SHOW_TIME 	
	property reset_beh_check;
		@(posedge rst_delay)
			(fsm1.pre_state == fsm1.SHOW_TIME);
	endproperty

//SHOW_TIME STATE CHECK - If pre_state is SHOW_TIME and if alarm_button is 1 then next_state should be SHOW_ALARM or 
//											  			if key not equal to NOKEY then next_state should be KEY_STORED or 
//											  			next_state should be SHOW_TIME itself
	property show_time_st_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.SHOW_TIME) |=> if($past(fsm1.alarm_button,1)) 
														(fsm1.pre_state == fsm1.SHOW_ALARM)
													else if ($past(fsm1.key,1) != $past(fsm1.NOKEY,1))
														(fsm1.pre_state == fsm1.KEY_STORED)
														else 
															($stable(fsm1.pre_state));					
	endproperty

//KEY_STORED STATE CHECK - If pre_state is KEY_STORED then next_state should be KEY_WAITED 
	property key_stored_st_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.KEY_STORED) |=>  (fsm1.pre_state == fsm1. KEY_WAITED);
	endproperty

//KEY_WAITED STATE CHECK - If pre_state is KEY_WAITED and if key equal to NOKEY, then next_state should be KEY_ENTRY or
//														  if time_out is 0, then next_state should be SHOW_TIME or
//														  next_state should be KEY_WAITED itself
	property key_waited_st_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.KEY_WAITED) |=> if ($past(fsm1.key,1) == $past(fsm1.NOKEY,1))
														(fsm1.pre_state == fsm1.KEY_ENTRY)
													else if ($past(fsm1.time_out,1) == 0 )
														(fsm1.pre_state == fsm1.SHOW_TIME)					
														else 
															($stable(fsm1.pre_state));
	endproperty


//KEY ENTRY STATE CHECK - If pre_state is KEY_ENTRY and if alarm_button is 1, then next_state should be SET_ALARM_TIME or
//														if time_button is 1, then next_state should be SET_CURRENT_TIME or
//														if time_out is 1, then next_state should be SHOW_TIME or   
//														if key not equal to NOKEY, then next_state should be KEY_STORED or
//														next_state should be KEY_ENTRY itself
	property key_entry_st_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.KEY_ENTRY) |=> if ($past(fsm1.alarm_button,1))
														(fsm1.pre_state == fsm1.SET_ALARM_TIME)								
													else if ($past(fsm1.time_button,1))
														(fsm1.pre_state == fsm1.SET_CURRENT_TIME)														
													else if ($past(fsm1.time_out,1) == 0)
														(fsm1.pre_state == fsm1.SHOW_TIME)																
													else if($past(fsm1.key,1) != $past(fsm1.NOKEY,1))
														(fsm1.pre_state == fsm1.KEY_STORED)																	
													else
														($stable(fsm1.pre_state));
	endproperty
	
//SHOW ALARM STATE CHECK - If pre_state is SHOW_ALARM and if alarm_button is 0, then next_state should be SHOW_TIME or
//														  next_state should be SHOW_ALARM itself
	property show_alarm_st_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.SHOW_ALARM) |=> if($past(fsm1.alarm_button,1) == 0)
														(fsm1.pre_state == fsm1. SHOW_TIME)
													else
														($stable(fsm1.pre_state));
	endproperty

//SET_ALARM TIME STATE CHECK - If pre_state is SET_ALARM_TIME then next_state should be SHOW_TIME 
	property set_alarm_time_st_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.SET_ALARM_TIME) |=>  (fsm1.pre_state == fsm1.SHOW_TIME);
	endproperty

//SET_CURRENT TIME STATE CHECK - If pre_state is SET_CURRENT_TIME then next_state should be SHOW_TIME 
	property set_current_time_st_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.SET_CURRENT_TIME) |=>  (fsm1.pre_state == fsm1.SHOW_TIME);
	endproperty

//ASSERTIONS FOR OUTPUT SIGNALS
//show_new_time - If pre_state is KEY_STORED or KEY_ENTRY or KEY_WAITED then show_new_time should be 1
	property show_new_time_check;
		@(posedge clock) disable iff(reset)
			((fsm1.pre_state == fsm1.KEY_STORED) || (fsm1.pre_state == fsm1.KEY_ENTRY) || (fsm1.pre_state == fsm1.KEY_WAITED)) |-> (fsm1.show_new_time == 1);
	endproperty

//show_a - If pre_state is SHOW_ALARM then show_a should be 1
	property show_a_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.SHOW_ALARM) |-> (fsm1.show_a == 1);
	endproperty

//load_new_a - If pre_state is SET_ALARM_TIME then load_new_a should be 1
	property load_new_a_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.SET_ALARM_TIME) |-> (fsm1.load_new_a == 1);
	endproperty

//load_new_c - If pre_state is SET_CURRENT_TIME then load_new_c and reset_count should be 1
	property load_new_c_reset_count_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.SET_CURRENT_TIME) |-> ((fsm1.load_new_c == 1) && ( fsm1.reset_count == 1));
	endproperty

//shift - If pre_state is KEY_STORED then shift should be 1
	property shift_check;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.KEY_STORED) |-> (fsm1.shift == 1);
	endproperty

//time_out - If pre_state is KEY_WAITED and if key not equal to 10 for continuous 2560 clock cycles, then time_out should be 1
	property time_out;
		@(posedge clock) disable iff(reset)
			(fsm1.pre_state == fsm1.KEY_WAITED) ##0 (fsm1.key!=10)[*2560]|=> (fsm1.time_out);
	endproperty


RESET_CHECK 		  	  : assert property (reset_beh_check);
SHOW_TIME_ST_CHECK 	  	  : assert property (show_time_st_check);
KEY_STORED_ST_CHECK	      : assert property (key_stored_st_check);	
KEY_WAITED_ST_CHECK	  	  : assert property (key_waited_st_check);	
KEY_ENTRY_ST_CHECK    	  : assert property (key_entry_st_check);
SHOW_ALARM_ST_CHECK	  	  : assert property (show_alarm_st_check);
SET_ALARM_TIME_ST_CHECK	  : assert property (set_alarm_time_st_check);
SET_CURRENT_TIME_ST_CHECK : assert property (set_current_time_st_check);
SHOW_NEW_TIME_OP_CHECK	  : assert property (show_new_time_check);
SHOW_A_OP_CHECK    	  	  : assert property (show_a_check);
LOAD_NEW_A_OP_CHECK   	  : assert property (load_new_a_check);
LOAD_NEW_C_OP_CHECK	  	  : assert property (load_new_c_reset_count_check);
SHIFT_OP_CHECK 		 	  : assert property (shift_check);
TIME_OUT_CHECK 		 	  : assert property (time_out);

endmodule
