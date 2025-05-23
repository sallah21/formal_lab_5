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
// Top-level interface properties for the “Formal verification part-0” practice
//   session
//-------------------------------------

`ifdef ASSERTIONS_EN

module dut_input_channel_control_properties #(
  // configurable parameters:
  parameter DATA_WIDTH = 'x                             // number of bits in a data word
)(
  input logic                  clk,                     //
  input logic                  nreset,                  //
  input logic                  first_cycle_of_proc_req, //
  // input interface:
  input logic                  in_en,                   //
  input logic                  in_valid,                // valid flag
  input logic                  in_ready,                // ready flag
  input logic [DATA_WIDTH-1:0] in_data,                 // data
  input logic                  in_data_last,            //
  // arbiter interface:
  input logic                  in_valid_arb,            // valid flag
  input logic [DATA_WIDTH-1:0] in_data_arb,             // data
  input logic                  in_data_last_arb,        // indicator of last data in a frame
  input logic                  arb_in_transferring      // indicator of arbitrating of a transfer from the input interface 0
);

  valid_ready_interface_properties  #(
    .INITIATOR_TO_TARGET_AS_ASSERTS (0),
    .TARGET_TO_INITIATOR_AS_ASSERTS (1),
    .DATA_WIDTH                     (DATA_WIDTH+1)
  )                                 valid_ready_properties_for_input_interface (
    // clocks and resets:
    .clk                            (clk),
    .nreset                         (nreset),
    // request/acknowledgment interface:
    .valid                          (in_valid),
    .ready                          (in_ready),
    .data                           ({in_data,
      in_data_last})
  );

endmodule

`endif // ASSERTIONS_EN
