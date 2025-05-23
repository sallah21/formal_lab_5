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

module dut_output_control_properties #(
  // configurable parameters:
  parameter DATA_WIDTH            = 'x,
  parameter IN_INTERFACE_ID_WIDTH = 'x,
  // local parameters used in port definitions:
  localparam FIFO_WIDTH = DATA_WIDTH + IN_INTERFACE_ID_WIDTH + 1
)(
  input logic                             clk,
  input logic                             nreset,
  input logic                             first_cycle_of_proc_req,
  input logic                             fifo_empty,
  input logic                             out_ready,
  input logic            [FIFO_WIDTH-1:0] fifo_out_data_packed,
  input logic                             fifo_re,
  input logic                             out_valid,
  input logic            [DATA_WIDTH-1:0] out_data,
  input logic [IN_INTERFACE_ID_WIDTH-1:0] out_data_source_id,
  input logic                             out_data_last,
  input logic                             out_last_data_sent
);

  //===========================================================================
  // properties, assertions and assumptions for the output interface
  //===========================================================================

  //---------------------------------------------------------------------------
  // standard properties of a valid/ready interface
  //---------------------------------------------------------------------------
  valid_ready_interface_properties #(
    .INITIATOR_TO_TARGET_AS_ASSERTS (1),
    .TARGET_TO_INITIATOR_AS_ASSERTS (0),
    .DATA_WIDTH                     (DATA_WIDTH+IN_INTERFACE_ID_WIDTH+1)
  ) valid_ready_properties_for_output_interface (
    // clocks and resets:
    .clk                            (clk),
    .nreset                         (nreset),
    // request/acknowledgment interface:
    .valid                          (out_valid),
    .ready                          (out_ready),
    .data                           ({out_data,
                                      out_data_source_id,
                                      out_data_last})
  );

endmodule

`endif // ASSERTIONS_EN