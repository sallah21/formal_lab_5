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

module dut_input_channel_control #(
  // configurable parameters:
  parameter DATA_WIDTH = 'x
)(
  // clocks and resets
  input logic                               clk,
  input logic                               nreset,

  // first cycle indicator
  input logic                               first_cycle_of_proc_req,

  // input interface:
  input logic                               in_en,
  input logic                               in_valid,                         // valid flag
  output logic                              in_ready,                         // ready flag
  input logic              [DATA_WIDTH-1:0] in_data,                          // data
  input logic                               in_data_last,

  // arbiter interface:
  output logic                               in_valid_arb,                         // valid flag
  output logic              [DATA_WIDTH-1:0] in_data_arb,                          // data
  output logic                               in_data_last_arb,                      // indicator of last data in a frame
  input logic                                arb_in_transferring            // indicator of arbitrating of a transfer from the input interface 0
);

  //===========================================================================
  // internal signals
  //===========================================================================
  logic                                     in_ready_c;                       // ready flag of input interface 0
  logic                                     in_transferring_c;                // flag indicating that data is being transferred through the input interface 0
  //-----
  logic                                     in_valid_arb_en_c;                    // enable flag for the in_valid_arb_r register
  logic                                     in_valid_arb_nxt_c;                   // next state of the in_valid_arb_r register
  logic                                     in_valid_arb_r;                       // indicator of valid data from input interface 0 in an internal register - register
  //-----
  logic                                     in_data_arb_en_c;                     // enable flag for registers storing internally registered data from input interface 0
  logic                    [DATA_WIDTH-1:0] in_data_arb_nxt_c;                    // next state of the in_data_arb_r register
  logic                                     in_data_last_arb_nxt_c;               // next state of the in_data_last_arb_r register
  logic                    [DATA_WIDTH-1:0] in_data_arb_r;                        // internally registered data from input interface 0 - register
  logic                                     in_data_last_arb_r;                   // internally registered indicator of last data in a frame from input interface 0

  //===========================================================================
  // internal logic
  //===========================================================================

  //---------------------------------------------------------------------------
  // ready flag of input interface
  //---------------------------------------------------------------------------
  always_comb in_ready_c = !first_cycle_of_proc_req &&
                        in_en &&
                        !in_data_last_arb_r &&
                        (!in_valid_arb_r ||
                        arb_in_transferring);

  //---------------------------------------------------------------------------
  // flag indicating that data is being transferred through the input
  //   interface
  //---------------------------------------------------------------------------
  always_comb in_transferring_c = in_ready_c &&
         in_valid;

  //---------------------------------------------------------------------------
  // indicator of valid data from input interface in an internal register -
  //   register
  //---------------------------------------------------------------------------
  // register enable flag:
  always_comb in_valid_arb_en_c  = !in_valid_arb_r ||
      arb_in_transferring;
  // next state of the register:
  always_comb in_valid_arb_nxt_c = in_transferring_c;
  // register:
  always_ff @(posedge clk or negedge nreset)
  begin
    if (!nreset)
      in_valid_arb_r <= 1'b0;
    else if (in_valid_arb_en_c)
      in_valid_arb_r <= in_valid_arb_nxt_c;
  end

  //---------------------------------------------------------------------------
  // internally registered data from input interface - registers
  //---------------------------------------------------------------------------
  // this internally registered indicator of last data in a frame is kept high
  //   from the time of a last data transfer to the beginning of a next frame;
  //   that is why, it can be used to block next transfers (after last data)
  //-----------------------------------
  // registers enable flag:
  always_comb in_data_arb_en_c       = first_cycle_of_proc_req ||
          in_transferring_c;
  // next states of the registers:
  always_comb in_data_arb_nxt_c      = in_data;
  always_comb in_data_last_arb_nxt_c = (first_cycle_of_proc_req) ? 1'b0 : in_data_last;
  // registers:
  always_ff @(posedge clk or negedge nreset)
  begin
    if (!nreset)
    begin
      in_data_arb_r      <= {DATA_WIDTH{1'b0}};
      in_data_last_arb_r <= 1'b0;
    end
    else if (in_data_arb_en_c)
    begin
      in_data_arb_r      <= in_data_arb_nxt_c;
      in_data_last_arb_r <= in_data_last_arb_nxt_c;
    end
  end

  //===========================================================================
  // output assignments
  //===========================================================================

  always_comb in_ready = in_ready_c;

  always_comb in_valid_arb = in_valid_arb_r;
  always_comb in_data_arb = in_data_arb_r;
  always_comb in_data_last_arb = in_data_last_arb_r;

endmodule