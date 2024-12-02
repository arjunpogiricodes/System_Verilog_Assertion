/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_ip_monitor.sv

Description	  	: 	monitor class for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------



class alarm_clock_ip_monitor extends uvm_monitor;
	
	//factory registration
	`uvm_component_utils(alarm_clock_ip_monitor)

	// configuration class handle
	alarm_clock_ip_agent_config ip_agt_cfg;
	
	//virtual interface handle
	
	virtual alarm_clock_if.IP_MON vif;
	
	//transaction class handle
	alarm_clock_trans data_to_rm;
	
	//analysis port handle
	uvm_analysis_port#(alarm_clock_trans)ap;
							   
	
	// Standard UVM Methods like constructor,post_randomize
   	extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern function void connect_phase(uvm_phase phase);
	extern task run_phase(uvm_phase phase);
	extern task collect_data();
endclass:alarm_clock_ip_monitor

//-----------------  constructor new method  -------------------//
//Add code for new()

function alarm_clock_ip_monitor :: new(string name,uvm_component parent);
	super.new(name,parent);
	ap = new("ap",this);
endfunction

function void alarm_clock_ip_monitor :: build_phase(uvm_phase phase);
	if(!uvm_config_db#(alarm_clock_ip_agent_config)::get(this,"","alarm_clock_ip_agent_config",ip_agt_cfg))
		`uvm_fatal(get_type_name(),"getting config object failed")
endfunction

function void alarm_clock_ip_monitor ::connect_phase(uvm_phase phase);
	this.vif = ip_agt_cfg.vif;
endfunction

task alarm_clock_ip_monitor ::run_phase(uvm_phase phase);
	forever
		collect_data();	
endtask

task alarm_clock_ip_monitor :: collect_data();

	data_to_rm = alarm_clock_trans::type_id::create("data_to_rm");

	//collecting alarm time	
	@(vif.ip_mon_cb);
	wait(vif.ip_mon_cb.key!=10);
	data_to_rm.alarm_ms_hr = vif.ip_mon_cb.key;
	wait(vif.ip_mon_cb.key ==10);
	@(vif.ip_mon_cb);
	wait(vif.ip_mon_cb.key!=10);
	data_to_rm.alarm_ls_hr = vif.ip_mon_cb.key;
	wait(vif.ip_mon_cb.key ==10);
	@(vif.ip_mon_cb);
	wait(vif.ip_mon_cb.key!=10);
	data_to_rm.alarm_ms_min = vif.ip_mon_cb.key;
	wait(vif.ip_mon_cb.key ==10);
	@(vif.ip_mon_cb);
	wait(vif.ip_mon_cb.key!=10);
	data_to_rm.alarm_ls_min = vif.ip_mon_cb.key;
	wait(vif.ip_mon_cb.key ==10);
	//@(vif.ip_mon_cb);
	data_to_rm.alarm_button = vif.ip_mon_cb.alarm_button;
	@(vif.ip_mon_cb);

	//collecting current time	
	@(vif.ip_mon_cb);
	wait(vif.ip_mon_cb.key!=10);
	data_to_rm.ms_hr = vif.ip_mon_cb.key;
	wait(vif.ip_mon_cb.key ==10);
	@(vif.ip_mon_cb);
	wait(vif.ip_mon_cb.key!=10);
	data_to_rm.ls_hr = vif.ip_mon_cb.key;
	wait(vif.ip_mon_cb.key ==10);
	@(vif.ip_mon_cb);
	wait(vif.ip_mon_cb.key!=10);
	data_to_rm.ms_min = vif.ip_mon_cb.key;
	wait(vif.ip_mon_cb.key ==10);
	@(vif.ip_mon_cb);
	wait(vif.ip_mon_cb.key!=10);
	data_to_rm.ls_min = vif.ip_mon_cb.key;
	wait(vif.ip_mon_cb.key ==10);
	@(vif.ip_mon_cb);
	data_to_rm.time_button = vif.ip_mon_cb.time_button;
	data_to_rm.fast_watch = vif.ip_mon_cb.fast_watch;

	@(vif.ip_mon_cb);


	`uvm_info(get_type_name(), $sformatf("data collected from monitor is %s",data_to_rm.sprint()),UVM_MEDIUM)

	ap.write(data_to_rm);
	
endtask 
