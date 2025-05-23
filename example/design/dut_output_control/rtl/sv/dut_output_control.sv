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

module dut_output_control #(
  // configurable parameters:
  parameter DATA_WIDTH = 'x,
  parameter IN_INTERFACE_ID_WIDTH = 'x,

  // local parameters used in port definitions:
  localparam FIFO_WIDTH = DATA_WIDTH + IN_INTERFACE_ID_WIDTH + 1
)(
  // clocks and resets
  input logic                               clk,
  input logic                               nreset,

  // first cycle indicator
  input logic                               first_cycle_of_proc_req,

  // FIFO interface
  input logic                               fifo_empty,
  input logic                               out_ready,
  input logic              [FIFO_WIDTH-1:0] fifo_out_data_packed,
  output logic                              fifo_re,

  // output interface
  output logic                              out_valid,
  output logic             [DATA_WIDTH-1:0] out_data,
  output logic  [IN_INTERFACE_ID_WIDTH-1:0] out_data_source_id,
  output logic                              out_data_last,
  output logic                              out_last_data_sent              // indicator that last output data has been sent out in a given frame - register
);

  //===========================================================================
  // internal signals
  //===========================================================================
  logic                                     out_valid_c;                       // output valid flag
  //-----
  logic                                     out_last_data_sent_en_c;           // enable flag for the out_last_data_sent_r register
  logic                                     out_last_data_sent_nxt_c;          // next state of the out_last_data_sent_r register
  //-----
  logic                    [DATA_WIDTH-1:0] fifo_out_data_unpacked_c;
  logic         [IN_INTERFACE_ID_WIDTH-1:0] fifo_out_data_source_id_unpacked_c;
  logic                                     fifo_out_data_last_unpacked_c;
  logic                                     out_last_data_sent_r;
  //-----
  logic                                     fifo_re_c;                       // output valid flag

  //===========================================================================
  // internal logic
  //===========================================================================
  always_comb fifo_re_c = !fifo_empty &&
                     out_ready;

  always_comb fifo_out_data_unpacked_c = fifo_out_data_packed[FIFO_WIDTH-1:IN_INTERFACE_ID_WIDTH+1];
  always_comb fifo_out_data_last_unpacked_c = fifo_out_data_packed[IN_INTERFACE_ID_WIDTH];
  always_comb fifo_out_data_source_id_unpacked_c = fifo_out_data_packed[IN_INTERFACE_ID_WIDTH-1:0];

  //---------------------------------------------------------------------------
  // output valid flag
  //---------------------------------------------------------------------------
  always_comb out_valid_c = !fifo_empty;


  //---------------------------------------------------------------------------
  // indicator that last output data has been sent out in a given frame -
  //   register
  //---------------------------------------------------------------------------
  // register enable flag:
  always_comb out_last_data_sent_en_c  = first_cycle_of_proc_req ||
                                    (out_valid_c &&
                                    out_ready &&
                                    fifo_out_data_last_unpacked_c);
  // next state of the register:
  always_comb out_last_data_sent_nxt_c = !first_cycle_of_proc_req;
  // register:
  always_ff @(posedge clk or negedge nreset)
  begin
    if (!nreset)
    out_last_data_sent_r <= 1'b0;
    else if (out_last_data_sent_en_c)
    out_last_data_sent_r <= out_last_data_sent_nxt_c;
  end

  //===========================================================================
  // output assignments
  //===========================================================================
  always_comb out_data = fifo_out_data_unpacked_c;
  always_comb out_data_source_id = fifo_out_data_source_id_unpacked_c;
  always_comb out_data_last = fifo_out_data_last_unpacked_c;
  always_comb out_valid = out_valid_c;
  always_comb out_last_data_sent = out_last_data_sent_r;
  always_comb fifo_re = fifo_re_c;

endmodule