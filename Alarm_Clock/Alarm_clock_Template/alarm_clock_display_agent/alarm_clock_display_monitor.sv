/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_display_monitor.sv

Description	  	: 	Display monitor class for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------



class alarm_clock_display_monitor extends uvm_monitor;
	
	//factory registration
	`uvm_component_utils(alarm_clock_display_monitor)

	bit busy=1;
	bit ending;
	// configuration class handle
	alarm_clock_display_agent_config disp_agt_cfg;
		
	//virtual interface handle
	
	virtual alarm_clock_if.DISPLAY_MON vif;
	
	//event
	uvm_event eve,eve1,eve2;
	
	//transaction class handle
	alarm_clock_display_trans data_to_sb;
	
	//analysis port handle
	uvm_analysis_port#(alarm_clock_display_trans)ap;
							   
	
	// Standard UVM Methods like constructor,post_randomize
    	extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern function void connect_phase(uvm_phase phase);
	extern task run_phase(uvm_phase phase);
	extern task collect_data();
	extern task collect_current_time();
	extern task collect_alarm_time();
	extern function void phase_ready_to_end(uvm_phase phase);

endclass:alarm_clock_display_monitor

//-----------------  constructor new method  -------------------//
//Add code for new()

function alarm_clock_display_monitor :: new(string name,uvm_component parent);
	super.new(name,parent);
	ap = new("ap",this);
endfunction

function void alarm_clock_display_monitor :: build_phase(uvm_phase phase);
	if(!uvm_config_db#(alarm_clock_display_agent_config)::get(this,"","alarm_clock_display_agent_config",disp_agt_cfg))
		`uvm_fatal(get_type_name(),"getting config object failed")
        //`uvm_info(get_type_name(), $sformatf("display agent config object is %p",disp_agt_cfg),UVM_MEDIUM)

	
endfunction

function void alarm_clock_display_monitor ::connect_phase(uvm_phase phase);
	this.vif = disp_agt_cfg.vif;
endfunction

task alarm_clock_display_monitor ::run_phase(uvm_phase phase);
  	eve = disp_agt_cfg.event_pool.get("eve");
	eve1 = disp_agt_cfg.event_pool.get("eve1");
	eve2 = disp_agt_cfg.event_pool.get("eve2");

  	forever
		begin
     		collect_data();
		disp_agt_cfg.no_of_data_collected++;
		if(disp_agt_cfg.no_of_data_collected == no_of_trans)
			busy =0;
		if(ending)
			phase.drop_objection(this);
		`uvm_info(get_type_name(),$sformatf("data collected from monitor is %s",data_to_sb.sprint()),UVM_MEDIUM)


		end
endtask

task alarm_clock_display_monitor :: collect_data();

	data_to_sb = alarm_clock_display_trans::type_id::create("data_to_sb");
	
	fork
	collect_current_time();
	collect_alarm_time();
	join
	ap.write(data_to_sb);
	eve2.trigger;
endtask

task alarm_clock_display_monitor :: collect_current_time();

	eve.wait_ptrigger();
	`uvm_info(get_type_name(),"THIS IS MONITOR RUN PHASE",UVM_MEDIUM)
	repeat(256*60*(disp_agt_cfg.ref_time))@(vif.display_mon_cb);
	//`uvm_info(get_type_name(),"THIS IS MONITOR RUN PHASE",UVM_MEDIUM)
	repeat(3)@(vif.display_mon_cb);

	data_to_sb.display_ls_min = vif.display_mon_cb.display_ls_min;
	data_to_sb.display_ms_min = vif.display_mon_cb.display_ms_min;
	data_to_sb.display_ls_hr = vif.display_mon_cb.display_ls_hr;
	data_to_sb.display_ms_hr = vif.display_mon_cb.display_ms_hr;

	
endtask

task alarm_clock_display_monitor :: collect_alarm_time();
	
	eve1.wait_ptrigger();
	
	repeat(2)@(vif.display_mon_cb);
	wait(vif.display_mon_cb.sound_alarm);
        data_to_sb.sound_alarm = vif.display_mon_cb.sound_alarm;

	repeat(2)@(vif.display_mon_cb);

	data_to_sb.alarm_ls_min = vif.display_mon_cb.display_ls_min;
	data_to_sb.alarm_ms_min = vif.display_mon_cb.display_ms_min;
	data_to_sb.alarm_ls_hr = vif.display_mon_cb.display_ls_hr;
	data_to_sb.alarm_ms_hr = vif.display_mon_cb.display_ms_hr;
        repeat(1)@(vif.display_mon_cb);

//	`uvm_info(get_type_name(),$sformatf("data collected from monitor is %s",data_to_sb.sprint()),UVM_MEDIUM)
	
endtask

function void alarm_clock_display_monitor::phase_ready_to_end(uvm_phase phase);

	if(phase.get_name == "run") 
		begin
			if (busy)
				begin
				ending =1;
				phase.raise_objection(this);
				end
		end
endfunction
 
