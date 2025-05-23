#-----------------------------------------------------------------------------
#
# Copyright 2024 Intel Corporation All Rights Reserved.
#
# The source code contained or described herein and all documents related
# to the source code ("Material") are owned by Intel Corporation or its
# suppliers or licensors. Title to the Material remains with Intel
# Corporation or its suppliers and licensors. The Material contains trade
# secrets and proprietary and confidential information of Intel or its
# suppliers and licensors. The Material is protected by worldwide copyright
# and trade secret laws and treaty provisions. No part of the Material may
# be used, copied, reproduced, modified, published, uploaded, posted,
# transmitted, distributed, or disclosed in any way without Intel's prior
# express written permission.
#
# No license under any patent, copyright, trade secret or other intellectual
# property right is granted to or conferred upon you by disclosure or
# delivery of the Materials, either expressly, by implication, inducement,
# estoppel or otherwise. Any license under such intellectual property rights
# must be express and approved by Intel in writing.
#
#-----------------------------------------------------------------------------

### Clear the environment
clear -all
check_sec -clear all

### Set flow variables
set MODULE_NAME dut_toplevel

### Import custom helper procedures used in this flow - no need to know the details

source "$::env(UNI_REPO_ROOT)/example/formal/common/procedures.tcl"

### For metrics and for organisation, we take the current time
set systemTime [tcl_clock seconds]
flow_log info "Runtime timestamp that will be used for this run: [tcl_clock format $systemTime -format "%H:%M:%S %d.%m.%Y"]"
set output_rundir_name [tcl_clock format $systemTime -format "${MODULE_NAME}_OUT_RUNDIR_%H:%M:%S__%d_%m_%Y"]
if {![file isdirectory output]} {
    flow_log debug "Creating output directory..."
    file mkdir output
} else {
    flow_log debug "Output directory already created."
}
flow_log debug "Creating run output dir..."
file mkdir "output/$output_rundir_name"

### After creating the output folders, get final write path for all output files
set complete_run_out_path "output/$output_rundir_name"

### Dump env for potential debug purposes
# my_parray is defined in procedures.tcl
# Adapted based on https://stackoverflow.com/questions/34221492/redirecting-the-parray-output-to-a-file-in-tcl

set envDumpData [my_parray env]
set envDumpFileId [open "$complete_run_out_path/.envdump" "w"]
puts $envDumpFileId $envDumpData
close $envDumpFileId


### Joined setup for sequence equivalence check
check_sec -setup \
          -spec_top dut_toplevel \
          -spec_analyze_opts { -sv12 -f /home/student/Documents/DS/FORMAL/sequence-equivalence-check-example/example/formal/sec/run/spec_files.f } \
          -spec_elaborate_opts { -bbox_mul 128 -bbox_div 128 -bbox_a 65536 } \
          -imp_top imp_dut_toplevel \
          -imp_analyze_opts { -sv12 -f /home/student/Documents/DS/FORMAL/sequence-equivalence-check-example/example/formal/sec/run/imp_files.f } \
          -imp_elaborate_opts { -bbox_mul 128 -bbox_div 128 -bbox_a 65536 }


### Map and waive signals that cannot be mapped automatically


### Provide clock and reset info
reset -expression !(nreset)
clock clk

### Sanity check of the interface mapping - very important that no errors or warnings are reported
check_sec -interface

### Run prove
check_sec -prove

### Get validity status of the proof
check_sec -signoff -get_valid_status

### Generate report
check_sec -signoff -detailed -force -file "$complete_run_out_path/$MODULE_NAME.sequence_eq_chk.rpt"
