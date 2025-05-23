//-----------------------------------------------------------------------------
//
// Copyright 2023 Intel Corporation All Rights Reserved.
//
// The source code contained or described herein and all documents related
// to the source code ("Material") are owned by Intel Corporation or its
// suppliers or licensors. Title to the Material remains with Intel
// Corporation or its suppliers and licensors. The Material contains trade
// secrets and proprietary and confidential information of Intel or its
// suppliers and licensors. The Material is protected by worldwide copyright
// and trade secret laws and treaty provisions. No part of the Material may
// be used, copied, reproduced, modified, published, uploaded, posted,
// transmitted, distributed, or disclosed in any way without Intel's prior
// express written permission.
//
// No license under any patent, copyright, trade secret or other intellectual
// property right is granted to or conferred upon you by disclosure or
// delivery of the Materials, either expressly, by implication, inducement,
// estoppel or otherwise. Any license under such intellectual property rights
// must be express and approved by Intel in writing.
//
//-----------------------------------------------------------------------------
// Binding of top-level interface properties for the “Formal verification
//   part-0” practice session
//-------------------------------------

`ifdef ASSERTIONS_EN

bind dut_toplevel dut_toplevel_interface_properties #(
  .DATA_WIDTH               (DATA_WIDTH),
  .FIFO_HEIGHT              (FIFO_HEIGHT)
) dut_toplevel_interface_properties (
  // clocks and resets:
  .clk                      (clk),
  .nreset                   (nreset),
  // processing control interface:
  .proc_req                 (proc_req),
  .proc_req_in0_en          (proc_req_in0_en),
  .proc_req_in0_arb_mode_id (proc_req_in0_arb_mode_id),
  .proc_req_in1_en          (proc_req_in1_en),
  .proc_req_in1_arb_mode_id (proc_req_in1_arb_mode_id),
  .proc_req_in2_en          (proc_req_in2_en),
  .proc_req_in2_arb_mode_id (proc_req_in2_arb_mode_id),
  .proc_ack                 (proc_ack),
  // input interface 0:
  .in0_valid                (in0_valid),
  .in0_ready                (in0_ready),
  .in0_data                 (in0_data),
  .in0_data_last            (in0_data_last),
  // input interface 1:
  .in1_valid                (in1_valid),
  .in1_ready                (in1_ready),
  .in1_data                 (in1_data),
  .in1_data_last            (in1_data_last),
  // input interface 2:
  .in2_valid                (in2_valid),
  .in2_ready                (in2_ready),
  .in2_data                 (in2_data),
  .in2_data_last            (in2_data_last),
  // output interface:
  .out_valid                (out_valid),
  .out_ready                (out_ready),
  .out_data                 (out_data),
  .out_data_source_id       (out_data_source_id),
  .out_data_last            (out_data_last)
);

`endif
