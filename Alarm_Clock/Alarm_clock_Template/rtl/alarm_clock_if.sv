/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_if.sv

Description	  	: 	Interface for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com 

Version		    :	1.0

************************************************************************/

interface alarm_clock_if(input logic clk);

	//interface signals
	logic[7:0]display_ls_min;
	logic[7:0]display_ms_min;
	logic[7:0]display_ls_hr;
    	logic[7:0]display_ms_hr;
	logic[3:0]key;
	logic alarm_button;
	logic time_button;
	logic fast_watch;
	
	logic reset;
	logic sound_alarm;
//	bit clock;

	//assign clk = clock;
	// clocking block for driver
	clocking ip_drv_cb @(posedge clk);
		output key;
		output alarm_button;
		output time_button;
		output fast_watch;
	endclocking
	
	//clocking block for monitor
	clocking ip_mon_cb @(posedge clk);
		input key;
		input alarm_button;
		input time_button;
		input fast_watch;
		input reset;
	endclocking
	
	//clocking block for monitor
	clocking display_mon_cb @(posedge clk);
		input display_ls_min;
		input display_ms_min;
		input display_ls_hr;
		input display_ms_hr;
		input sound_alarm;
	endclocking
	
	// modports
	modport IP_DRV (clocking ip_drv_cb,output reset);
	modport IP_MON	(clocking ip_mon_cb);
	modport DISPLAY_MON (clocking display_mon_cb);
	
endinterface: alarm_clock_if
	
