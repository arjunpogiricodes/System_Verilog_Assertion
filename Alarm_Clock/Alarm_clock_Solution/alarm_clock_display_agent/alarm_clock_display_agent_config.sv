/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  alarm_clock_display_agent_config.sv

Description	  	: 	display agent configuration class for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------


class alarm_clock_display_agent_config extends uvm_object;
	
	//factory registration
	`uvm_object_utils(alarm_clock_display_agent_config)

	//configurable parameters

	
	virtual alarm_clock_if vif;
	
	rand bit[5:0]ref_time;
	
	uvm_event_pool event_pool;

	// Standard UVM Methods like constructor
    	extern function new(string name ="");
	int no_of_data_collected;
	
endclass:alarm_clock_display_agent_config

//-----------------  constructor new method  -------------------//
//Add code for new()

function alarm_clock_display_agent_config :: new(string name ="");
	super.new(name);
endfunction


 
