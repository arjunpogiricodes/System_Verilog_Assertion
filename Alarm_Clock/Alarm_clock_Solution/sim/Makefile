#Makefile for SVA Alarm Clock

# SIMULATOR = Questa for Mentor's Questasim
# SIMULATOR = VCS for Synopsys's VCS

SIMULATOR = VCS
FSDB_PATH=/home/cad/eda/SYNOPSYS/VERDI_2022/verdi/T-2022.06-SP1/share/PLI/VCS/LINUX64

RTL= ../rtl/*
work= work #library name
SVTB1= ../alarm_clock_env/top.sv
INC = +incdir+../alarm_clock_env +incdir+../alarm_clock_test +incdir+../alarm_clock_ip_agent +incdir+../alarm_clock_display_agent +incdir+../alarm_clock_assertions
SVTB2 = ../alarm_clock_test/alarm_clock_pkg.sv
SVTB3 = ../alarm_clock_assertions/fsm_assertions.sv
VSIMOPT= -vopt -voptargs=+acc 
VSIMCOV= -coverage -sva 
VSIMBATCH1= -c -do  " log -r /* ;run -all; exit"
VSIMBATCH2= -c -do  " log -r /* ;coverage save -onexit alarm_cov1;run -all; exit"
VSIMBATCH3= -c -do  " log -r /* ;coverage save -onexit alarm_cov2;run -all; exit"
VSIMBATCH4= -c -do  " log -r /* ;coverage save -onexit alarm_cov3;run -all; exit"

help:
	@echo =============================================================================================================
	@echo "! USAGE   	-- 			 make target              					!"
	@echo "! clean   	=>  clean the earlier log and intermediate files.       				!"
	@echo "! sv_cmp     	=>  Create library and compile the code.                   				!"
	@echo "! run_sim   	=>  run the simulation in batch mode.               					!"
	@echo "! run_test	=>  clean, compile & run the simulation for alarm_clock_test in batch mode. 		!" 
	@echo "! TC1		=>  clean, compile & run the simulation for alarm_clock_rand_test in batch mode.	!" 
	@echo "! TC2		=>  clean, compile & run the simulation for alarm_clock_current_time_test in batch mode	!"
	@echo "! TC3		=>  clean, compile & run the simulation for alarm_clock_child_test in batch mode.	!" 
	@echo "! view_wave 	=>  To view the waveform of alarm_clock_test	    				!" 
	@echo "! view_wave1 	=>  To view the waveform of alarm_clock_rand_test	    				!" 
	@echo "! view_wave2 	=>  To view the waveform of alarm_clock_current_time_test	    		  	!" 
	@echo "! view_wave3 	=>  To view the waveform of alarm_clock_child_test	  	  			!" 
	@echo "! regress  	=>  clean, compile and run TC1,TC2 & TC3 test cases in batch mode.		   	!"
	@echo "! report    	=>  To merge coverage reports for testcases TC1,TC2 & TC3  and  convert to html format	!"
	@echo "! cov       	=>  To open merged coverage report in html format					!"
	@echo ====================================================================================================================

clean : clean_$(SIMULATOR)
sv_cmp : sv_cmp_$(SIMULATOR)
run_test : run_test_$(SIMULATOR)
TC1 : TC1_$(SIMULATOR)
TC2 : TC2_$(SIMULATOR)
TC3 : TC3_$(SIMULATOR)
view_wave1 : view_wave1_$(SIMULATOR)
view_wave2 : view_wave2_$(SIMULATOR)
view_wave3 : view_wave3_$(SIMULATOR)
view_wave : view_wave_$(SIMULATOR)
regress : regress_$(SIMULATOR)
report : report_$(SIMULATOR)
cov : cov_$(SIMULATOR)

# ----------------------------- Start of Definitions for Mentor's Questa Specific Targets -------------------------------#

sv_cmp_Questa:
	vlib $(work)
	vmap work $(work)
	vlog -work $(work) $(RTL) $(INC) $(SVTB2) $(SVTB3) $(SVTB1) 	
	
run_test_Questa:sv_cmp
	vsim -cvgperinstance $(VSIMOPT) $(VSIMCOV) $(VSIMBATCH1)  -wlf wave_file.wlf -l test.log  -sv_seed random work.top +UVM_TESTNAME=alarm_clock_test
	
TC1_Questa:sv_cmp
	vsim -cvgperinstance $(VSIMOPT) $(VSIMCOV) $(VSIMBATCH2) -wlf wave_file1.wlf -l test1.log -sv_seed 1257422047  work.top +UVM_TESTNAME=alarm_clock_rand_test +UVM_VERBOSITY=UVM_LOW
	vcover report  -cvg  -details -nocompactcrossbins -codeAll -assert -directive -html alarm_cov1
	
TC2_Questa:
	vsim -cvgperinstance $(VSIMOPT) $(VSIMCOV) $(VSIMBATCH3)  -wlf wave_file2.wlf -l test2.log  -sv_seed 3161712080 work.top +UVM_TESTNAME=alarm_clock_current_time_test
	vcover report  -cvg  -details -nocompactcrossbins -codeAll -assert -directive -html alarm_cov2
	
TC3_Questa:
	vsim -cvgperinstance $(VSIMOPT) $(VSIMCOV) $(VSIMBATCH4)  -wlf wave_file3.wlf -l test3.log  -sv_seed random  work.top +UVM_TESTNAME=alarm_clock_child_test
	vcover report  -cvg  -details -nocompactcrossbins -codeAll -assert -directive -html alarm_cov3

regress_Questa: TC1_Questa TC2_Questa TC3_Questa report_Questa cov_Questa

report_Questa:
	vcover merge alarm_cov.ucdb alarm_cov_generated.ucdb  alarm_cov1 alarm_cov2 alarm_cov3
	vcover report -cvg -details -nocompactcrossbins -codeAll -assert -directive -html alarm_cov.ucdb

view_wave_Questa:
	vsim -view wave_file.wlf&

view_wave1_Questa:
	vsim -view wave_file1.wlf&
	
view_wave2_Questa:
	vsim -view wave_file2.wlf&
	
view_wave3_Questa:
	vsim -view wave_file3.wlf&
	
cov_Questa:
	firefox covhtmlreport/index.html&
	
clean_Questa:
	rm -rf transcript* *log*  vsim.wlf fcover* covhtml* alarm_cov* *.wlf modelsim.ini
	clear

# ------------------------------- End of Definitions for Mentor's Questa Specific Targets -------------------------------#

# ----------------------------- Start of Definitions for Synopsys's VCS Specific Targets -------------------------------#


sv_cmp_VCS:
	vcs -l vcs.log -timescale=1ns/1ns -sverilog -ntb_opts uvm -debug_access+all -full64 -cm assert -kdb  -assert enable_diag -lca -P $(FSDB_PATH)/novas.tab $(FSDB_PATH)/pli.a $(RTL) $(INC) $(SVTB2) $(SVTB3) $(SVTB1)
	      
run_test_VCS:	clean_VCS  sv_cmp_VCS
	./simv -a vcs.log +fsdbfile+wave_file.fsdb -cm assert_enable_coverage=1 -cm_dir ./alarm_cov0 +ntb_random_seed_automatic -assert verbose=noattempt +UVM_TESTNAME=alarm_clock_test 
	urg -dir alarm_cov0.vdb -format both
	
TC1_VCS:sv_cmp_VCS	
	./simv -a vcs.log +fsdbfile+wave_file1.fsdb -cm assert_enable_coverage=1 -cm_dir ./alarm_cov1 +ntb_random_seed_automatic -assert verbose=noattempt +UVM_TESTNAME=alarm_clock_rand_test +UVM_VERBOSITY=UVM_LOW 
	urg -dir alarm_cov1.vdb -format both
	
TC2_VCS:
	./simv -a vcs.log +fsdbfile+wave_file2.fsdb -cm assert_enable_coverage=1 -cm_dir ./alarm_cov2 +ntb_random_seed_automatic -assert verbose=noattempt +UVM_TESTNAME=alarm_clock_current_time_test 
	urg -dir alarm_cov2.vdb -format both
	
TC3_VCS:
	./simv -a vcs.log +fsdbfile+wave_file3.fsdb  -cm assert_enable_coverage=1 -cm_dir ./alarm_cov3 +ntb_random_seed_automatic -assert verbose=noattempt +UVM_TESTNAME=alarm_clock_child_test 
	urg -dir alarm_cov3.vdb -format both
	
view_wave_VCS: 
	verid -ssf wave_file.fsdb	
view_wave1_VCS: 
	verdi -ssf wave_file1.fsdb
	
view_wave2_VCS: 
	verdi -ssf wave_file2.fsdb

view_wave3_VCS: 
	verdi -ssf wave_file3.fsdb
		
report_VCS:
	urg -dir alarm_cov0.vdb alarm_cov1.vdb alarm_cov2.vdb alarm_cov3.vdb -dbname merged_dir/merged_test -format both 

regress_VCS: clean_VCS TC1_VCS TC2_VCS TC3_VCS report_VCS

cov_VCS:
	verdi -cov -covdir merged_dir.vdb
	# firefox urgReport/mem_cov.html&

clean_VCS:
	rm -rf simv* csrc* *.tmp *.vpd *.vdb *.key *.log *hdrs.h urgReport* novas* vdCov* verdi*
	clear

# ----------------------------- END of Definitions for :Synopsys's VCS Specific Targets -------------------------------#
