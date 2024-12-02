# Makefile for fifo verilog testbench 


# SIMULATOR = Questa for Mentor's Questasim
# SIMULATOR = VCS for Synopsys's VCS

SIMULATOR = VCS


FSDB_PATH=/home/cad/eda/SYNOPSYS/VERDI_2022/verdi/T-2022.06-SP1/share/PLI/VCS/LINUX64
TB = ../duv_tb/*
work= work

COVOP = -coveropt 3 +cover=bcft
VSIMOPT= -vopt -voptargs=+acc 
VSIMCOV= -coverage -sva
 
VSIMBATCH = -c -do "log -r /* ; coverage save -onexit fifo_cov; run -all;exit"
  
help:
	@echo ===============================================================================
	@echo " USAGE   	--  make target                             				"
	@echo " clean   	=>  clean the earlier log and intermediate files.       	"
	@echo " sv_cmp    	=>  Create library and compile the code.                   	"
	@echo " run_sim     =>  run the simulation in batch mode.                   	"
	@echo " run_test	=>  clean, compile & run the simulation in batch mode.		" 
	@echo " view_wave    => To view the waveform						"
	@echo " cov		=> To view the coverage report					"
	@echo ===============================================================================
	
clean : clean_$(SIMULATOR)
run_sim : run_sim_$(SIMULATOR)
sv_cmp : sv_cmp_$(SIMULATOR)
run_test : run_test_$(SIMULATOR)
view_wave:view_$(SIMULATOR)
cov:cov_$(SIMULATOR)

# ---- Start of Definitions for Mentor's Questa Specific Targets -----#

sv_cmp_Questa:
	vlib $(work)
	vmap work $(work)
	vlog -work $(work) $(TB)
	
run_sim_Questa:
	vsim  $(VSIMOPT) $(VSIMCOV) $(VSIMBATCH) -wlf wave_file.wlf -l test.log work.tb_fifo 
	vcover report  -cvg  -details -codeAll -assert -directive  -html fifo_cov
	 
clean_Questa:
	rm -rf transcript* *log* fcover* covhtml* mem_cov* *.wlf modelsim.ini work
	clear

run_test_Questa: clean_Questa sv_cmp_Questa run_sim_Questa

view_Questa: 
	vsim -view wave_file.wlf

cov_Questa:
	firefox covhtml/index.html&

# ---- End of Definitions for Mentor's Questa Specific Targets -----#

# ---- Start of Definitions for Synopsys VCS Specific Targets----# 

sv_cmp_VCS:
	vcs -l vcs.log -sverilog -debug_access+all -full64 -cm assert -kdb -lca -P $(FSDB_PATH)/novas.tab $(FSDB_PATH)/pli.a  $(TB)

run_sim_VCS: 
	./simv -a vcs.log -cm assert_enable_coverage=1 -cm_dir ./cov ntb_random_seed=2231849661
	urg -dir cov.vdb -format both -report urgReport
	
clean_VCS:
	rm -rf simv* csrc* *.tmp *.key *.log *.vdb *hdrs.h urgReport* novas* vdCov* verdi*
	clear 
	
run_test_VCS: clean_VCS sv_cmp_VCS run_sim_VCS	
	
view_VCS: 
	verdi -ssf novas.fsdb

cov_VCS:
	 verdi -cov -covdir cov.vdb
# ---- End of Definitions for Synopsys VCS Specific Targets -----#
