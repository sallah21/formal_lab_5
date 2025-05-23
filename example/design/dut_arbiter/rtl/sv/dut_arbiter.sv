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

module dut_arbiter #(
  // configurable parameters:
  parameter DATA_WIDTH = 'x,
  parameter IN_INTERFACE_ID_WIDTH = 'x,
  parameter ARB_MODES_NUM = 'x,

  // local parameters used in port definitions:
  localparam ARB_MODE_ID_WIDTH = (ARB_MODES_NUM == 1) ? 1 : $clog2(ARB_MODES_NUM)
)(
  // clocks and resets
  input logic                               clk,
  input logic                               nreset,

  // indicator of first cycle of processing, acts as a soft reset
  input logic                               first_cycle_of_proc_req,

  // channel 0 interface
  input logic                               in0_en,
  input logic     [ARB_MODE_ID_WIDTH-1:0]   in0_arb_mode_id_en,
  input logic                               in0_valid,
  input logic            [DATA_WIDTH-1:0]   in0_data,
  input logic                               in0_data_last,
  output logic                              arb_in0_transferring,

  // channel 1 interface
  input logic                               in1_en,
  input logic     [ARB_MODE_ID_WIDTH-1:0]   in1_arb_mode_id_en,
  input logic                               in1_valid,
  input logic            [DATA_WIDTH-1:0]   in1_data,
  input logic                               in1_data_last,
  output logic                              arb_in1_transferring,

  // channel 2 interface
  input logic                               in2_en,
  input logic     [ARB_MODE_ID_WIDTH-1:0]   in2_arb_mode_id_en,
  input logic                               in2_valid,
  input logic            [DATA_WIDTH-1:0]   in2_data,
  input logic                               in2_data_last,
  output logic                              arb_in2_transferring,

  // arbiter output interface
  output logic           [DATA_WIDTH-1:0]   arb_data,
  output logic[IN_INTERFACE_ID_WIDTH-1:0]   arb_data_source_id,
  output logic                              arb_data_last,
  output logic                              arb_data_valid,
  input logic                               arb_data_ready
);

  //===========================================================================
  // internal signals
  //===========================================================================
  logic                                     arb_in0_transferring_c;            // indicator of arbitrating of a transfer from the input interface 0
  logic                                     arb_in1_transferring_c;            // indicator of arbitrating of a transfer from the input interface 1
  logic                                     arb_in2_transferring_c;            // indicator of arbitrating of a transfer from the input interface 2
  //-----
  logic                                     arb_transferring_c;                // indicator of any data being transferred through the arbiter
  //-----
  logic                    [DATA_WIDTH-1:0] arb_data_c;                        // arbitrated data
  logic                                     arb_data_last_c;                   // indicator that arbitrated data is last data in a frame
  logic         [IN_INTERFACE_ID_WIDTH-1:0] arb_data_source_id_c;              // arbitrated source (input interface) ID
  //-----
  logic                                     arb_last_data_source_id_en_c;      // enable flag for arb_last_data_source_id_r register
  logic         [IN_INTERFACE_ID_WIDTH-1:0] arb_last_data_source_id_nxt_c;     // next state of the arb_last_data_source_id_r register
  logic         [IN_INTERFACE_ID_WIDTH-1:0] arb_last_data_source_id_r;         // lastly arbitrated source (input interface) ID - register

  //===========================================================================
  // internal logic
  //===========================================================================

  //---------------------------------------------------------------------------
  // indicator of arbitrating of a transfer from the input interface 0
  //---------------------------------------------------------------------------
  always_comb
  begin
  case (in0_arb_mode_id_en)
    //-----
    1'b0:
      // simple round robin:
      arb_in0_transferring_c = arb_data_ready &&
                               in0_valid &&
                               ((arb_last_data_source_id_r == 2'b10) ||
                                ((arb_last_data_source_id_r == 2'b01) && !in2_valid) ||
                                ((arb_last_data_source_id_r == 2'b00) && !in1_valid && !in2_valid));
    //-----
    1'b1:
      // not supported arbitration mode:
      arb_in0_transferring_c = 1'b0;
    //-----
    default:
      arb_in0_transferring_c = {ARB_MODE_ID_WIDTH{1'bx}};
    //-----
  endcase
  end

  //---------------------------------------------------------------------------
  // indicator of arbitrating of a transfer from the input interface 1
  //---------------------------------------------------------------------------
  always_comb
  begin
  case (in1_arb_mode_id_en)
    //-----
    1'b0:
      // simple round robin:
      arb_in1_transferring_c = arb_data_ready &&
                               in1_valid &&
                               ((arb_last_data_source_id_r == 2'b00) ||
                                ((arb_last_data_source_id_r == 2'b10) && !in0_valid) ||
                                ((arb_last_data_source_id_r == 2'b01) && !in2_valid && !in0_valid));
    //-----
    1'b1:
      // not supported arbitration mode:
      arb_in1_transferring_c = 1'b0;
    //-----
    default:
      arb_in1_transferring_c = {ARB_MODE_ID_WIDTH{1'bx}};
    //-----
  endcase
  end

  //---------------------------------------------------------------------------
  // indicator of arbitrating of a transfer from the input interface 2
  //---------------------------------------------------------------------------
  always_comb
  begin
  case (in2_arb_mode_id_en)
    //-----
    1'b0:
      // simple round robin:
      arb_in2_transferring_c = arb_data_ready &&
                               in2_valid &&
                               ((arb_last_data_source_id_r == 2'b01) ||
                                ((arb_last_data_source_id_r == 2'b00) && !in1_valid) ||
                                ((arb_last_data_source_id_r == 2'b10) && !in0_valid && !in1_valid));
    //-----
    1'b1:
      // not supported arbitration mode:
      arb_in2_transferring_c = 1'b0;
    //-----
    default:
      arb_in2_transferring_c = {ARB_MODE_ID_WIDTH{1'bx}};
    //-----
  endcase
  end

  //---------------------------------------------------------------------------
  // arbitrated data
  //---------------------------------------------------------------------------
  always_comb arb_data_c = (arb_in0_transferring_c) ? in0_data :
                      (arb_in1_transferring_c) ? in1_data :
                                                 in2_data;

  //---------------------------------------------------------------------------
  // indicator that arbitrated data is last data in a frame
  //---------------------------------------------------------------------------
  always_comb arb_data_last_c = (!in0_en ||
          (in0_data_last &&
           (!in0_valid ||
            arb_in0_transferring_c))) &&
         (!in1_en ||
          (in1_data_last &&
           (!in1_valid ||
            arb_in1_transferring_c))) &&
         (!in2_en ||
          (in2_data_last &&
           (!in2_valid ||
            arb_in2_transferring_c)));

  //---------------------------------------------------------------------------
  // arbitrated source (input interface) ID
  //---------------------------------------------------------------------------
  always_comb arb_data_source_id_c = (arb_in0_transferring_c) ? 2'b00 :
                                (arb_in1_transferring_c) ? 2'b01 :
                                                           2'b10;

  //---------------------------------------------------------------------------
  // indicator of any data being transferred through the arbiter
  //---------------------------------------------------------------------------
  always_comb arb_transferring_c = arb_in0_transferring_c ||
                              arb_in1_transferring_c ||
                              arb_in2_transferring_c;

  //---------------------------------------------------------------------------
  // lastly arbitrated source (input interface) ID - register
  //---------------------------------------------------------------------------
  // register enable flag:
  always_comb arb_last_data_source_id_en_c  = first_cycle_of_proc_req ||
                                         arb_transferring_c;
  // next state of the register:
  always_comb arb_last_data_source_id_nxt_c = (first_cycle_of_proc_req) ?
                                         // reset at the beginning of processing:
                                              2'b10 :
                                         // normal processing:
                                              arb_data_source_id_c;
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      arb_last_data_source_id_r <= {IN_INTERFACE_ID_WIDTH{1'b0}};
    else if (arb_last_data_source_id_en_c)
      arb_last_data_source_id_r <= arb_last_data_source_id_nxt_c;
    end


  //===========================================================================
  // output assignments
  //===========================================================================

  always_comb arb_in0_transferring = arb_in0_transferring_c;
  always_comb arb_in1_transferring = arb_in1_transferring_c;
  always_comb arb_in2_transferring = arb_in2_transferring_c;
  
  always_comb arb_data = arb_data_c;
  always_comb arb_data_source_id = arb_data_source_id_c;
  always_comb arb_data_last = arb_data_last_c;
  always_comb arb_data_valid = arb_transferring_c;

  //===========================================================================
  // internal properties
  //===========================================================================
  `ifdef ASSERTIONS_EN

  //---------------------------------------------------------------------------
  // no more than one indicator of arbitrating of a transfer from an input
  //   interface can be high at the same time
  //---------------------------------------------------------------------------
  property pr__not_more_than_one_arb_in_transferring_high_at_the_same_time;
    @(posedge clk) disable iff (!nreset)
      (arb_in0_transferring_c ||
       arb_in1_transferring_c ||
       arb_in2_transferring_c)
        |->
      ($onehot({arb_in0_transferring_c,
                arb_in1_transferring_c,
                arb_in2_transferring_c}));
  endproperty

  `endif


endmodule