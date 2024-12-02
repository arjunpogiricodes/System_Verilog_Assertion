/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename	    :   alarm_clock_ip_seqs.sv

Description 	:   sequence class for alarm_clock
  
Author Name		:   shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/


//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------

 
// Extend ram_wbase_seq from uvm_sequence parameterized by write_xtn 
class alarm_clock_base_seq extends uvm_sequence #(alarm_clock_trans);  
	
  // Factory registration using `uvm_object_utils

	`uvm_object_utils(alarm_clock_base_seq)  
	//------------------------------------------
	// METHODS
	//------------------------------------------

	// Standard UVM Methods:
  extern function new(string name ="");
	
endclass

//-----------------  constructor new method  -------------------//
function alarm_clock_base_seq::new(string name ="");
	 super.new(name);
endfunction



//Extend alarm_clock_rand_seq from alarm_clock_base_seq;
class alarm_clock_rand_seq extends alarm_clock_base_seq;

  // Factory registration using `uvm_object_utils
	`uvm_object_utils(alarm_clock_rand_seq)

	//------------------------------------------
	// METHODS
	//------------------------------i------------

	// Standard UVM Methods:
  extern function new(string name ="");
  extern task body();
	
endclass

//-----------------  constructor new method  -------------------//
function alarm_clock_rand_seq::new(string name = "");
	 super.new(name);
endfunction

//-----------------  task body method  -------------------//
//Generate 10 transactions of type write_xtn 
//create req instance
//start_item(req)
//assert for randomization
//finish_item(req)

task alarm_clock_rand_seq::body();
  // repeat(10)
	    begin
	    	 req=alarm_clock_trans::type_id::create("req");
	    	 start_item(req);
	    	 assert(req.randomize());
	    	 finish_item(req); 	
	    end
endtask


//Extend alarm_clock_current_time_seq from alarm_clock_base_seq;
class alarm_clock_current_time_seq extends alarm_clock_base_seq;

  // Factory registration using `uvm_object_utils
	`uvm_object_utils(alarm_clock_current_time_seq)

	//------------------------------------------
	// METHODS
	//------------------------------i------------

	// Standard UVM Methods:
  extern function new(string name ="");
  extern task body();
	
endclass

//-----------------  constructor new method  -------------------//
function alarm_clock_current_time_seq::new(string name = "");
	 super.new(name);
endfunction

//-----------------  task body method  -------------------//
//Generate 10 transactions of type write_xtn 
//create req instance
//start_item(req)
//assert for randomization
//finish_item(req)

task alarm_clock_current_time_seq::body();
  // repeat(10)
	    begin
	    	 req=alarm_clock_trans::type_id::create("req");
	    	 start_item(req);
	    	 assert(req.randomize()with {{alarm_ms_hr,alarm_ls_hr,alarm_ms_min,alarm_ls_min}-{ms_hr,ls_hr,ms_min,ls_min} <10;});
	    	 finish_item(req); 	
	    end
endtask
