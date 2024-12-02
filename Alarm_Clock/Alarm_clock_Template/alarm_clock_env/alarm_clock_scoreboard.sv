/************************************************************************
  
Copyright 2019 - Maven Silicon Softech Pvt Ltd.  
  
www.maven-silicon.com 
  
All Rights Reserved. 
This source code is an unpublished work belongs to Maven Silicon Softech Pvt Ltd. 
It is not to be shared with or used by any third parties who have not enrolled for our paid 
training courses or received any written authorization from Maven Silicon.
  
Filename		:  	alarm_clock_scoreboard.sv

Description	  	: 	scoreboard class for Alarm Clock
  
Author Name	  	:   Shanthi V A

Support e-mail	: 	techsupport_vm@maven-silicon.com  

Version		    :	1.0

************************************************************************/

//------------------------------------------
// CLASS DESCRIPTION
//------------------------------------------



class alarm_clock_scoreboard extends uvm_scoreboard;
	
	//factory registration
	`uvm_component_utils(alarm_clock_scoreboard)

	// tlm interface
	uvm_tlm_analysis_fifo#(alarm_clock_display_trans)fifo_disp;
	
	uvm_tlm_analysis_fifo#(alarm_clock_trans)fifo_ip;
	
	alarm_clock_trans ip_data,ip_cov_data;

        alarm_clock_display_trans op_data,op_cov_data,disp_cov_data;
					   
	
	alarm_clock_env_config ecfg;
	// Standard UVM Methods like constructor
   	extern function new(string name ,uvm_component parent);
	extern function void build_phase(uvm_phase phase);
	extern task run_phase (uvm_phase phase);
        extern task check_alarm_time();
	extern task check_current_time();
	extern task calc_current_time();

        covergroup cg_ip_data;
		option.per_instance=1;

		CURRENT_TIME_MS_HR	: coverpoint ip_cov_data.ms_hr{ bins b1 = {0};
								        bins b2 = {1};
								        bins b3 = {2};
                                                                        illegal_bins b4 = {[3:9]};}

		CURRENT_TIME_LS_HR	: coverpoint ip_cov_data.ls_hr{ bins b1 = {0};
								        bins b2 = {1};
                                                                        bins b3 = {2};
								        bins b4 = {3};
								        bins b5 = {4};
								        bins b6 = {5};
								        bins b7 = {6};
								        bins b8 = {7};
								        bins b9 = {8}; 
								        bins b0 = {9};}

		CURRENT_TIME_MS_MIN	: coverpoint ip_cov_data.ms_min{ bins b1 = {0};
								         bins b2 = {1};
                                                                         bins b3 = {2};
								         bins b4 = {3};
								         bins b5 = {4};
								         bins b6 = {5};
									illegal_bins b7 = {[6:9]};}


		CURRENT_TIME_LS_MIN	: coverpoint ip_cov_data.ls_min{bins b1 = {0};
								        bins b2 = {1};
                                                                        bins b3 = {2};
								        bins b4 = {3};
								        bins b5 = {4};
								        bins b6 = {5};
								        bins b7 = {6};
								        bins b8 = {7};
								        bins b9 = {8}; 
								        bins b0 = {9};}
		
		//CURRENT_TIME_MS_HR_TRANSITION	: coverpoint ip_cov_data.ms_hr{bins t1 = (0=>1);
             	//									    t2 = (1=>2);}
               // CURRENT_TIME_MS_HR_TRANSITION	: coverpoint ip_cov_data.ms_hr{bins t1 = {1=>2;} }


		ALARM_TIME_MS_HR	: coverpoint ip_cov_data.alarm_ms_hr{bins mshr[] = {[0:2]};}
		ALARM_TIME_LS_HR	: coverpoint ip_cov_data.alarm_ls_hr{bins lshr[] = {[0:9]};}
		ALARM_TIME_MS_MIN	: coverpoint ip_cov_data.alarm_ms_min{bins msmin[] = {[0:5]};}
		ALARM_TIME_LS_MIN	: coverpoint ip_cov_data.alarm_ls_min{bins lsmin[] = {[0:9]};}

		TIME_BUTTON		: coverpoint ip_cov_data.time_button { bins b1 = {1};}
		ALARM_BUTTON		: coverpoint ip_cov_data.alarm_button { bins b1 = {1};}
	        FAST_WATCH		: coverpoint ip_cov_data.fast_watch;

	
	endgroup

	covergroup cg_disp_data;
		option.per_instance=1;

		DISP_CURRENT_TIME_MS_HR	: coverpoint disp_cov_data.display_ms_hr{bins mshr[] = {[0:2]};}
		DISP_CURRENT_TIME_LS_HR	: coverpoint disp_cov_data.display_ls_hr{bins lshr[] = {[0:9]};}
		DISP_CURRENT_TIME_MS_MIN: coverpoint disp_cov_data.display_ms_min{bins msmin[] = {[0:5]};}
		DISP_CURRENT_TIME_LS_MIN: coverpoint disp_cov_data.display_ls_min{bins lsmin[] = {[0:9]};}

	
	endgroup



endclass:alarm_clock_scoreboard

//-----------------  constructor new method  -------------------//
//Add code for new()

function alarm_clock_scoreboard :: new(string name,uvm_component parent);
	super.new(name,parent);
	fifo_disp = new("fifo_disp",this);
	fifo_ip = new("fifo_ip",this);
	cg_ip_data = new();
	cg_disp_data = new();
endfunction

function void  alarm_clock_scoreboard ::build_phase(uvm_phase phase);
	if(!uvm_config_db#(alarm_clock_env_config)::get(this,"","alarm_clock_env_config",ecfg))
		`uvm_fatal(get_type_name(),"getting config object failed")
endfunction

task alarm_clock_scoreboard ::run_phase(uvm_phase phase);

forever
	begin
	fifo_ip.get(ip_data);
        //ip_data.print();
	fifo_disp.get(op_data);
	//op_data.print();
	check_alarm_time();
	check_current_time();
	ip_cov_data = new ip_data; 
	disp_cov_data = new op_data;
	cg_ip_data.sample();
	cg_disp_data.sample();
       end

endtask
	
task alarm_clock_scoreboard ::check_alarm_time();

	if({ip_data.alarm_ms_hr,ip_data.alarm_ls_hr,ip_data.alarm_ms_min,ip_data.alarm_ls_min} == {op_data.alarm_ms_hr,op_data.alarm_ls_hr,op_data.alarm_ms_min,op_data.alarm_ls_min})
		`uvm_info(get_type_name(),"SOUND ALARM IS WORKING PROPERLY",UVM_LOW)
	else
		`uvm_error(get_type_name(),"SOUND ALARM IS NOT WORKING PROPERLY")
endtask

task alarm_clock_scoreboard ::calc_current_time();

	if(ip_data.fast_watch ==0)
	begin
   	for(int i=0;i<ecfg.ref_time;i++)
		begin:A
		  if(ip_data.ls_min == 9)
		  	 begin:B 
				if(ip_data.ms_min == 5)
					begin:C
					ip_data.ms_min =0;
					ip_data.ls_min =0;
						if(ip_data.ms_hr==2)
							begin
								if(ip_data.ls_hr==3)
									begin
									ip_data.ls_hr = 0;
									ip_data.ms_hr = 0;
									end

								else
									begin
									ip_data.ls_hr = ip_data.ls_hr+1'b1;
									ip_data.ms_hr = ip_data.ms_hr;
									end
							end

						else
							begin
								if(ip_data.ls_hr==9)
									begin
									ip_data.ls_hr = 0;
									ip_data.ms_hr = ip_data.ms_hr+1'b1;
									end

								else
									begin
									ip_data.ls_hr = ip_data.ls_hr+1'b1;
									ip_data.ms_hr = ip_data.ms_hr;
									end
							end
	
							

					end:C
				else 
					begin:D
					ip_data.ls_min = 0;
					ip_data.ms_min = ip_data.ms_min+1'b1;
				        ip_data.ls_hr = ip_data.ls_hr;
					ip_data.ms_hr = ip_data.ms_hr;
					end
			end		
								 
		else
		   begin
		    	ip_data.ms_min = ip_data.ms_min;
			ip_data.ls_min =ip_data.ls_min+1'b1;
                        ip_data.ls_hr = ip_data.ls_hr;
			ip_data.ms_hr = ip_data.ms_hr;
		   end
		end:A
      end

      else
	begin
	for(int i=0;i<ecfg.ref_time;i++)
		begin
		 	if(ip_data.ms_hr!= 2)
				begin:E
					if(ip_data.ls_hr == 9)
						begin
							
							ip_data.ls_hr=0;
							ip_data.ms_hr=ip_data.ms_hr+1'b1;
							//ip_data.ms_min = ip_data.ms_min;
							//ip_data.ls_min = ip_data.ls_min;
						end
					else
					        begin
						  	ip_data.ls_hr=ip_data.ls_hr+1'b1;
							ip_data.ms_hr=ip_data.ms_hr;
							//ip_data.ms_min = ip_data.ms_min;
							//ip_data.ls_min = ip_data.ls_min;

						end
					end:E

			else
				begin:F
					if(ip_data.ls_hr ==3)
						begin
						   	ip_data.ls_hr=0;
							ip_data.ms_hr=0;
							//ip_data.ms_min = ip_data.ms_min;
							//ip_data.ls_min = ip_data.ls_min;

						end
					else 
					        begin
							ip_data.ls_hr=ip_data.ls_hr+1'b1;
							ip_data.ms_hr=ip_data.ms_hr;
							//ip_data.ms_min = ip_data.ms_min;
							//ip_data.ls_min = ip_data.ls_min;

						end
				end:F
			`uvm_info(get_type_name(),$sformatf("ms_hr =%d,ls_hr=%d",ip_data.ms_hr,ip_data.ls_hr),UVM_MEDIUM)
		end
	end
endtask

task alarm_clock_scoreboard ::check_current_time();
		
	calc_current_time();
	ip_data.print();
	if({ip_data.ms_hr,ip_data.ls_hr,ip_data.ms_min,ip_data.ls_min} == {op_data.display_ms_hr,op_data.display_ls_hr,op_data.display_ms_min,op_data.display_ls_min})
		`uvm_info(get_type_name(),"CURRENT TIME IS WORKING PROPERLY",UVM_LOW)
	else
		`uvm_error(get_type_name(),"CURRENT TIME IS NOT WORKING PROPERLY")
	
endtask







 
