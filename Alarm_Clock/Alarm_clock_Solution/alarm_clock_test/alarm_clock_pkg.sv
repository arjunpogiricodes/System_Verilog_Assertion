/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_pkg.sv

Description	  	: 	package for Alarm Clock
  
Author Name	  	:  	Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

package alarm_clock_pkg;

	import uvm_pkg::*;
	int no_of_trans =1;

	`include "uvm_macros.svh"

	`include "alarm_clock_ip_agent_config.sv"
	`include "alarm_clock_display_agent_config.sv"
	`include "alarm_clock_env_config.sv"

	`include "alarm_clock_trans.sv"
	`include "alarm_clock_ip_driver.sv"
	`include "alarm_clock_ip_monitor.sv"
	`include "alarm_clock_ip_agent.sv"
	`include "alarm_clock_ip_seq.sv"

	`include "alarm_clock_display_trans.sv"
	`include "alarm_clock_display_monitor.sv"
	`include "alarm_clock_display_agent.sv"

	
	`include "alarm_clock_scoreboard.sv"
	`include "alarm_clock_env.sv"

	`include "alarm_clock_test.sv"

endpackage

	

	


