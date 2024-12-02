/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_ip_driver.sv

Description	  	: 	driver class for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------



class alarm_clock_ip_driver extends uvm_driver#(alarm_clock_trans);
	
	//factory registration
	`uvm_component_utils(alarm_clock_ip_driver)

	// configuration class handle
	alarm_clock_ip_agent_config ip_agt_cfg;

	//virtual interface handle
	
	virtual alarm_clock_if.IP_DRV vif;
	
	//event
	uvm_event eve,eve1,eve2;

	int k;					   
	
	// Standard UVM Methods like constructor,post_randomize
   	extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern function void connect_phase(uvm_phase phase);
	extern task run_phase(uvm_phase phase);
	extern task drive_item(alarm_clock_trans xtn);
	extern task set_current_time(alarm_clock_trans xtn);
	extern task set_alarm_time(alarm_clock_trans xtn);

endclass:alarm_clock_ip_driver

//-----------------  constructor new method  -------------------//
//Add code for new()

function alarm_clock_ip_driver :: new(string name,uvm_component parent);
	super.new(name,parent);
endfunction

function void alarm_clock_ip_driver :: build_phase(uvm_phase phase);
	if(!uvm_config_db#(alarm_clock_ip_agent_config)::get(this,"","alarm_clock_ip_agent_config",ip_agt_cfg))
		`uvm_fatal(get_type_name(),"getting config object failed")

	
endfunction

function void alarm_clock_ip_driver ::connect_phase(uvm_phase phase);
	this.vif = ip_agt_cfg.vif;
endfunction

task alarm_clock_ip_driver::run_phase(uvm_phase phase);

	eve = ip_agt_cfg.event_pool.get("eve");
	eve1 = ip_agt_cfg.event_pool.get("eve1");
	eve2 = ip_agt_cfg.event_pool.get("eve2");

	repeat(2)@(vif.ip_drv_cb);
	vif.reset <= 1'b1;
	repeat(2)@(vif.ip_drv_cb);
	vif.reset <= 1'b0;
	
	forever
	begin
		seq_item_port.get_next_item(req);
		drive_item(req);
		seq_item_port.item_done();
	end

endtask

task alarm_clock_ip_driver :: drive_item(alarm_clock_trans xtn);
	//`uvm_info(get_type_name(),$sformatf("data received in driver is %s",xtn.sprint()),UVM_MEDIUM)
	if(k!=0)
		eve2.wait_ptrigger();
	set_alarm_time(xtn);
	set_current_time(xtn);
	k++;
endtask



task alarm_clock_ip_driver :: set_alarm_time(alarm_clock_trans xtn);
	//driving ms_hr
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= xtn.alarm_ms_hr;
	repeat(3)@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= 10;
	@(vif.ip_drv_cb);

	
	//driving ls_hr
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= xtn.alarm_ls_hr;
	repeat(3)@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= 10;
	@(vif.ip_drv_cb);

	//driving ms_min
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= xtn.alarm_ms_min;
	repeat(3)@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= 10;
	@(vif.ip_drv_cb);

	//driving ls_min
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= xtn.alarm_ls_min;
	repeat(3)@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= 10;
	@(vif.ip_drv_cb);
	

	
	vif.ip_drv_cb.alarm_button <= 1'b1;
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.alarm_button <= 1'b0;
	eve1.trigger();



endtask

task alarm_clock_ip_driver :: set_current_time(alarm_clock_trans xtn);
	//driving ms_hr
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= xtn.ms_hr;
	repeat(3)@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= 10;
	@(vif.ip_drv_cb);

	
	//driving ls_hr
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= xtn.ls_hr;
	repeat(3)@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= 10;
	@(vif.ip_drv_cb);

	//driving ms_min
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= xtn.ms_min;
	repeat(3)@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= 10;
	@(vif.ip_drv_cb);

	//driving ls_min
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= xtn.ls_min;
	repeat(3)@(vif.ip_drv_cb);
	vif.ip_drv_cb.key <= 10;
	@(vif.ip_drv_cb);
	

	
	vif.ip_drv_cb.time_button <= 1'b1;
	vif.ip_drv_cb.fast_watch  <= xtn.fast_watch;
	@(vif.ip_drv_cb);
	vif.ip_drv_cb.time_button <= 1'b0;
	eve.trigger();



endtask



 
