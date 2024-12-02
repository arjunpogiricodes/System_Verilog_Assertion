/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_ip_agent.sv

Description	  	: 	input agent class for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------



class alarm_clock_ip_agent extends uvm_agent;
	
	//factory registration
	`uvm_component_utils(alarm_clock_ip_agent)

	// configuration class handle
	alarm_clock_ip_agent_config ip_agt_cfg;
	
	// driver,monitor & sequencer handles
	alarm_clock_ip_driver drv;
	alarm_clock_ip_monitor mon;
	uvm_sequencer#(alarm_clock_trans) seqr;
	
						   
	
	// Standard UVM Methods like constructor,post_randomize
    	extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern function void connect_phase(uvm_phase phase);
endclass:alarm_clock_ip_agent

//-----------------  constructor new method  -------------------//
//Add code for new()

function alarm_clock_ip_agent :: new(string name,uvm_component parent);
	super.new(name,parent);
endfunction

function void alarm_clock_ip_agent :: build_phase(uvm_phase phase);
	if(!uvm_config_db#(alarm_clock_ip_agent_config)::get(this,"","alarm_clock_ip_agent_config",ip_agt_cfg))
		`uvm_fatal(get_type_name(),"getting config object failed")
	mon = alarm_clock_ip_monitor::type_id::create("mon",this);
	if(ip_agt_cfg.is_active ==UVM_ACTIVE)
		begin	
			drv = alarm_clock_ip_driver::type_id::create("drv",this);
			seqr = uvm_sequencer#(alarm_clock_trans)::type_id::create("seqr",this);
		end
endfunction

function void alarm_clock_ip_agent ::connect_phase(uvm_phase phase);
	if(ip_agt_cfg.is_active ==UVM_ACTIVE)
		drv.seq_item_port.connect(seqr.seq_item_export);
endfunction




 
