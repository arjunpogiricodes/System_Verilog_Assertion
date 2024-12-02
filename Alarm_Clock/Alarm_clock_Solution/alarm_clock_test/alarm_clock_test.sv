/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_test.sv

Description	  	: 	test class for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------



class alarm_clock_test extends uvm_test;
	
	//factory registration
	`uvm_component_utils(alarm_clock_test)

	// configuration class handle
	alarm_clock_env_config ecfg;
	alarm_clock_ip_agent_config ip_cfg;
	alarm_clock_display_agent_config disp_cfg;
	
	//environment handle
	alarm_clock_env env;
	
	bit has_ip_agent = 1;
	bit has_display_agent =1;
				   
	
	// Standard UVM Methods like constructor
   	extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern function void end_of_elaboration_phase(uvm_phase phase);
endclass:alarm_clock_test

//-----------------  constructor new method  -------------------//
//Add code for new()

function alarm_clock_test :: new(string name,uvm_component parent);
	super.new(name,parent);
endfunction

function void alarm_clock_test :: build_phase(uvm_phase phase);

	ecfg = alarm_clock_env_config::type_id::create("ecfg");
	
	if(has_display_agent)
		begin
			disp_cfg = alarm_clock_display_agent_config ::type_id::create("disp_cfg");
			if(!uvm_config_db#(virtual alarm_clock_if)::get(this,"","vif",disp_cfg.vif))
				`uvm_fatal(get_type_name(),"getting interface failed")
			disp_cfg.ref_time = {$random}%10;
			ecfg.disp_cfg = disp_cfg;
			disp_cfg.event_pool=ecfg.event_pool;
			ecfg.ref_time = disp_cfg.ref_time;
			`uvm_info(get_type_name(),$sformatf("ref_time generated is %d",ecfg.ref_time),UVM_MEDIUM)
		end
		
	if(has_ip_agent)
		begin
			ip_cfg = alarm_clock_ip_agent_config ::type_id::create("ip_cfg");	
		
			if(!uvm_config_db#(virtual alarm_clock_if)::get(this,"","vif",ip_cfg.vif))
				`uvm_fatal(get_type_name(),"getting interface failed")
			ip_cfg.is_active = UVM_ACTIVE;
			ecfg.ip_cfg=ip_cfg;
			ip_cfg.event_pool=ecfg.event_pool;
		end
	
	uvm_config_db#(alarm_clock_env_config)::set(this,"*","alarm_clock_env_config",ecfg);
	env = alarm_clock_env::type_id::create("env",this);
	
endfunction

function void alarm_clock_test :: end_of_elaboration_phase(uvm_phase phase);
	uvm_top.print_topology;
endfunction




class alarm_clock_rand_test extends alarm_clock_test;

	`uvm_component_utils(alarm_clock_rand_test)

	// Standard UVM Methods like constructor
   	extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern task run_phase(uvm_phase phase);
endclass : alarm_clock_rand_test


function alarm_clock_rand_test :: new(string name,uvm_component parent);
	super.new(name,parent);
endfunction

function void alarm_clock_rand_test :: build_phase(uvm_phase phase);
	super.build_phase(phase);
endfunction


task alarm_clock_rand_test ::run_phase(uvm_phase phase);

	alarm_clock_rand_seq seq;

	phase.raise_objection(this);
	seq = alarm_clock_rand_seq::type_id::create("seq");
	repeat(10)
	seq.start(env.ip_agt.seqr);
	//repeat(256*60*60)@(ip_cfg.vif.clk);
	phase.drop_objection(this);
endtask


 class alarm_clock_current_time_test extends alarm_clock_test;

	`uvm_component_utils(alarm_clock_current_time_test)

	// Standard UVM Methods like constructor
   	extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern task run_phase(uvm_phase phase);
endclass : alarm_clock_current_time_test


function alarm_clock_current_time_test :: new(string name,uvm_component parent);
	super.new(name,parent);
endfunction

function void alarm_clock_current_time_test :: build_phase(uvm_phase phase);
	super.build_phase(phase);
endfunction


task alarm_clock_current_time_test ::run_phase(uvm_phase phase);

	alarm_clock_current_time_seq seq;

	phase.raise_objection(this);
	seq = alarm_clock_current_time_seq::type_id::create("seq");
	repeat(20)
	seq.start(env.ip_agt.seqr);
	//repeat(256*60*60)@(ip_cfg.vif.clk);
	phase.drop_objection(this);
endtask


class alarm_clock_child_test extends alarm_clock_test;

	`uvm_component_utils(alarm_clock_child_test)

	// Standard UVM Methods like constructor
   	extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern task run_phase(uvm_phase phase);
endclass : alarm_clock_child_test


function alarm_clock_child_test :: new(string name,uvm_component parent);
	super.new(name,parent);
endfunction

function void alarm_clock_child_test :: build_phase(uvm_phase phase);
	super.build_phase(phase);
	set_type_override_by_type(alarm_clock_trans::get_type(),
		                  alarm_clock_child_trans::get_type());
endfunction


task alarm_clock_child_test ::run_phase(uvm_phase phase);

	alarm_clock_current_time_seq seq;

	phase.raise_objection(this);
	seq = alarm_clock_current_time_seq::type_id::create("seq");
	repeat(20)
	seq.start(env.ip_agt.seqr);
	//repeat(256*60*60)@(ip_cfg.vif.clk);
	phase.drop_objection(this);
endtask


