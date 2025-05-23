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

module dut_processing_control #(
  // configurable parameters:
  parameter ARB_MODES_NUM = 'x,

  // local parameters used in port definitions:
  localparam ARB_MODE_ID_WIDTH              = (ARB_MODES_NUM == 1) ? 1 : $clog2(ARB_MODES_NUM)        // width of an ID of an arbitration mode
)(
  // clocks and resets
  input logic                               clk,
  input logic                               nreset,

  // input interfaces
  input logic                               proc_req,                          // processing request
  output logic                              proc_ack,                          // processing acknowledgement
  input logic                               proc_req_in0_en,                   // input interface 0 - enable flag
  input logic       [ARB_MODE_ID_WIDTH-1:0] proc_req_in0_arb_mode_id,          // input interface 0 - arbitration mode ID
  input logic                               proc_req_in1_en,                   // input interface 1 - enable flag
  input logic       [ARB_MODE_ID_WIDTH-1:0] proc_req_in1_arb_mode_id,          // input interface 1 - arbitration mode ID
  input logic                               proc_req_in2_en,                   // input interface 2 - enable flag
  input logic       [ARB_MODE_ID_WIDTH-1:0] proc_req_in2_arb_mode_id,          // input interface 2 - arbitration mode ID

  // indicator of last data
  input logic                               out_last_data_sent,

  // channel enable
  output logic                              in0_en,
  output logic                              in1_en,
  output logic                              in2_en,

  // arbiter mode select
  output logic                              in0_arb_mode_id_en,
  output logic                              in1_arb_mode_id_en,
  output logic                              in2_arb_mode_id_en,

  // first cycle indicator
  output logic                              first_cycle_of_proc_req
);

  //===========================================================================
  // internal signals
  //===========================================================================
  logic                                     proc_req_in_prev_cycle_nxt_c;      // next state of the proc_req_in_prev_cycle_r register
  logic                                     proc_req_in_prev_cycle_r;          // state of the processing request in a previous cycle - register
  //-----
  logic                                     first_cycle_of_proc_req_c;         // indicator of a first cycle of the processing request
  //-----
  logic                                     proc_req_params_en_c;              // enable flag for registers storing parameters of a processing request
  logic                                     in0_en_nxt_c;                      // next state of the in0_en_r register
  logic             [ARB_MODE_ID_WIDTH-1:0] in0_arb_mode_id_en_nxt_c;          // next state of the in0_arb_mode_id_en_r register
  logic                                     in1_en_nxt_c;                      // next state of the in1_en_r register
  logic             [ARB_MODE_ID_WIDTH-1:0] in1_arb_mode_id_en_nxt_c;          // next state of the in1_arb_mode_id_en_r register
  logic                                     in2_en_nxt_c;                      // next state of the in2_en_r register
  logic             [ARB_MODE_ID_WIDTH-1:0] in2_arb_mode_id_en_nxt_c;          // next state of the in2_arb_mode_id_en_r register
  logic                                     in0_en_r;                          // input interface 0 - enable flag - register
  logic             [ARB_MODE_ID_WIDTH-1:0] in0_arb_mode_id_en_r;              // input interface 0 - arbitration mode ID - register
  logic                                     in1_en_r;                          // input interface 1 - enable flag - register
  logic             [ARB_MODE_ID_WIDTH-1:0] in1_arb_mode_id_en_r;              // input interface 1 - arbitration mode ID - register
  logic                                     in2_en_r;                          // input interface 2 - enable flag - register
  logic             [ARB_MODE_ID_WIDTH-1:0] in2_arb_mode_id_en_r;              // input interface 2 - arbitration mode ID - register
  //-----
  logic                                     proc_ack_en_c;                     // enable flag for the proc_ack_r register
  logic                                     proc_ack_nxt_c;                    // next state of the proc_ack_r register
  logic                                     proc_ack_r;                        // processing acknowledgement - register

  //===========================================================================
  // internal logic
  //===========================================================================

  //---------------------------------------------------------------------------
  // state of the processing request in a previous cycle - register
  //---------------------------------------------------------------------------
  // next state of the register:
  always_comb proc_req_in_prev_cycle_nxt_c = proc_req;
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      proc_req_in_prev_cycle_r <= 1'b0;
    else
      proc_req_in_prev_cycle_r <= proc_req_in_prev_cycle_nxt_c;
    end

  //---------------------------------------------------------------------------
  // indicator of a first cycle of the processing request
  //---------------------------------------------------------------------------
  always_comb first_cycle_of_proc_req_c = proc_req &&
                                     !proc_req_in_prev_cycle_r;

  //---------------------------------------------------------------------------
  // processing request parameters - registers
  //---------------------------------------------------------------------------
  // these parameters are registered here to avoid inout paths through this
  //   module
  //-----------------------------------
  // registers enable flag:
  always_comb proc_req_params_en_c     = first_cycle_of_proc_req_c;
  // next states of the registers:
  always_comb in0_en_nxt_c             = proc_req_in0_en;
  always_comb in0_arb_mode_id_en_nxt_c = proc_req_in0_arb_mode_id;
  always_comb in1_en_nxt_c             = proc_req_in1_en;
  always_comb in1_arb_mode_id_en_nxt_c = proc_req_in1_arb_mode_id;
  always_comb in2_en_nxt_c             = proc_req_in2_en;
  always_comb in2_arb_mode_id_en_nxt_c = proc_req_in2_arb_mode_id;
  // registers:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      begin
      in0_en_r             <= 1'b0;
      in0_arb_mode_id_en_r <= {ARB_MODE_ID_WIDTH{1'b0}};
      in1_en_r             <= 1'b0;
      in1_arb_mode_id_en_r <= {ARB_MODE_ID_WIDTH{1'b0}};
      in2_en_r             <= 1'b0;
      in2_arb_mode_id_en_r <= {ARB_MODE_ID_WIDTH{1'b0}};
      end
    else if (proc_req_params_en_c)
      begin
      in0_en_r             <= in0_en_nxt_c;
      in0_arb_mode_id_en_r <= in0_arb_mode_id_en_nxt_c;
      in1_en_r             <= in1_en_nxt_c;
      in1_arb_mode_id_en_r <= in1_arb_mode_id_en_nxt_c;
      in2_en_r             <= in2_en_nxt_c;
      in2_arb_mode_id_en_r <= in2_arb_mode_id_en_nxt_c;
      end
    end

  //---------------------------------------------------------------------------
  // processing acknowledgement - register
  //---------------------------------------------------------------------------
  // register enable flag:
  always_comb proc_ack_en_c  = proc_ack_r ||
                          (!first_cycle_of_proc_req_c &&
                           (out_last_data_sent ||
                            (!in0_en_r &&
                             !in1_en_r &&
                             !in2_en_r)));
  // next state of the register:
  always_comb proc_ack_nxt_c = proc_req;
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      proc_ack_r <= 1'b0;
    else if (proc_ack_en_c)
      proc_ack_r <= proc_ack_nxt_c;
    end

  //===========================================================================
  // output assignments
  //===========================================================================

  always_comb in0_en = in0_en_r;
  always_comb in1_en = in1_en_r;
  always_comb in2_en = in2_en_r;

  always_comb in0_arb_mode_id_en = in0_arb_mode_id_en_r;
  always_comb in1_arb_mode_id_en = in1_arb_mode_id_en_r;
  always_comb in2_arb_mode_id_en = in2_arb_mode_id_en_r;

  always_comb first_cycle_of_proc_req = first_cycle_of_proc_req_c;

  always_comb proc_ack = proc_ack_r;

endmodule