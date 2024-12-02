/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_trans.sv

Description	  	: 	Input transaction class for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------


class alarm_clock_trans extends uvm_sequence_item;
	
	//factory registration
	`uvm_object_utils(alarm_clock_trans)

	//transaction class properties

	rand bit[3:0]ls_min;
	rand bit[3:0]ms_min;
	rand bit[3:0]ls_hr;
    	rand bit[3:0]ms_hr;

	rand bit[3:0]alarm_ls_min;
	rand bit[3:0]alarm_ms_min;
	rand bit[3:0]alarm_ls_hr;
    	rand bit[3:0]alarm_ms_hr;

	rand bit alarm_button;
	rand bit time_button;
	rand bit fast_watch;
	rand bit[2:0]no_of_cycles;
	
	constraint valid_ls_min{ls_min inside{[0:9]};alarm_ls_min inside {[0:9]};}
	constraint valid_ms_min{ms_min inside{[0:5]}; alarm_ms_min inside{[0:5]};}
	constraint valid_ls_hr{if(ms_hr==2) ls_hr inside{[0:3]};
						   else ls_hr inside{[0:9]};
				if(alarm_ms_hr==2) alarm_ls_hr inside{[0:3]};
						   else alarm_ls_hr inside{[0:9]};}
   	constraint valid_ms_hr{ms_hr inside{[0:2]};alarm_ms_hr inside{[0:2]};}
	constraint valid_cycles{no_of_cycles inside{ [3:8]};}						   
	constraint valid_fast_watch{if(unsigned'({alarm_ms_hr,alarm_ls_hr,alarm_ms_min,alarm_ls_min}-{ms_hr,ls_hr,ms_min,ls_min})>10)
								fast_watch ==1;
				else fast_watch == 0;}
	

	// Standard UVM Methods like constructor,post_randomize
    	extern function new(string name = "alarm_clock_trans");
	extern function void do_print(uvm_printer printer); 
endclass:alarm_clock_trans

//-----------------  constructor new method  -------------------//
//Add code for new()

function alarm_clock_trans :: new(string name = "alarm_clock_trans");
	super.new(name);
endfunction

function void  alarm_clock_trans::do_print (uvm_printer printer);
	super.do_print(printer); 
	//                   string name   				bitstream value    	 size       radix for printing
	printer.print_field( "ls_min", 				this.ls_min, 	   	 4,		 UVM_DEC	);
	printer.print_field( "ms_min", 				this.ms_min, 	   	 4,		 UVM_DEC	);
   	printer.print_field( "ls_hr", 				this.ls_hr, 	   	 4,		 UVM_DEC	);	
	printer.print_field( "ms_hr", 				this.ms_hr, 	   	 4,		 UVM_DEC	);
	printer.print_field( "alarm_ls_min", 			this.alarm_ls_min, 	 4,		 UVM_DEC	);
	printer.print_field( "alarm_ms_min", 			this.alarm_ms_min, 	 4,		 UVM_DEC	);
   	printer.print_field( "alarm_ls_hr", 			this.alarm_ls_hr,  	 4,		 UVM_DEC	);	
	printer.print_field( "alarm_ms_hr", 			this.alarm_ms_hr,   	 4,		 UVM_DEC	);
	printer.print_field( "time button", 			this.time_button, 	 1,		 UVM_DEC	);  
	printer.print_field( "alarm button", 			this.alarm_button, 	 1,		 UVM_DEC	);
	printer.print_field( "fast watch", 			this.fast_watch, 	 1,		 UVM_DEC	);
endfunction


//////////////////////////Extended class////////////////////////
class alarm_clock_child_trans extends alarm_clock_trans;

	//factory registration
	`uvm_object_utils(alarm_clock_child_trans)

	extern function new(string name = "alarm_clock_child_trans");

	constraint valid_ls_min_c{ls_min inside{2,4,5,7,9};}
	constraint valid_ms_min_c{ms_min inside{3};}
	constraint valid_ls_hr_c {ls_hr inside {2,8,9};}
   	constraint valid_ms_hr{ms_hr inside{2};}



endclass

function alarm_clock_child_trans :: new(string name = "alarm_clock_child_trans");
	super.new(name);
endfunction

