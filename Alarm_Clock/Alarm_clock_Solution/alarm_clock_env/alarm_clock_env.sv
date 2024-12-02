/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_env.sv

Description	  	: 	environment class for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------



class alarm_clock_env extends uvm_env;
	
	//factory registration
	`uvm_component_utils(alarm_clock_env)

	// configuration class handle
	alarm_clock_env_config ecfg;
	
	// agents,scoreboard & ref_model handles
	alarm_clock_ip_agent ip_agt;
	alarm_clock_display_agent disp_agt;
	//alarm_clock_ref_model ref_mod;
	alarm_clock_scoreboard sb;
	
						   
	
	// Standard UVM Methods like constructor,post_randomize
    extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern function void connect_phase(uvm_phase phase);
endclass:alarm_clock_env

//-----------------  constructor new method  -------------------//
//Add code for new()

function alarm_clock_env :: new(string name,uvm_component parent);
	super.new(name,parent);
endfunction

function void alarm_clock_env :: build_phase(uvm_phase phase);
	if(!uvm_config_db#(alarm_clock_env_config)::get(this,"","alarm_clock_env_config",ecfg))
		`uvm_fatal(get_type_name(),"getting config object failed")
	
	if(ecfg.has_ip_agent)
		begin
			uvm_config_db#(alarm_clock_ip_agent_config)::set(this,"ip_agt*","alarm_clock_ip_agent_config",ecfg.ip_cfg);
			ip_agt = alarm_clock_ip_agent::type_id::create("ip_agt",this);
		end
		
	if(ecfg.has_display_agent)
		begin
			uvm_config_db#(alarm_clock_display_agent_config)::set(this,"disp_agt*","alarm_clock_display_agent_config",ecfg.disp_cfg);
			disp_agt = alarm_clock_display_agent::type_id::create("disp_agt",this);	
		end
		
	/*if(ecfg.has_ref_model)
		ref_mod = alarm_clock_ref_model::type_id::create("ref_mod",this);*/
		
	if(ecfg.has_scoreboard)
		sb = alarm_clock_scoreboard::type_id::create("sb",this);	
endfunction

function void alarm_clock_env ::connect_phase(uvm_phase phase);
	//ref_mod.get_port.connect(sb.get_imp);
	ip_agt.mon.ap.connect(sb.fifo_ip.analysis_export);
	disp_agt.mon.ap.connect	(sb.fifo_disp.analysis_export);
endfunction




 
