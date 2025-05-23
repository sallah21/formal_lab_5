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
// DUT top-level module for the “Formal verification part-0” practice session
//-------------------------------------

module dut_toplevel #(
  // configurable parameters:
  parameter DATA_WIDTH                      = dut_params_pkg::DATA_WIDTH,      // number of bits in a data word
  parameter FIFO_HEIGHT                     = dut_params_pkg::FIFO_HEIGHT,     // number of entries in the FIFO
  // local parameters used in port definitions:
  localparam ARB_MODES_NUM                  = 2,                               // number of supported arbitration modes
  localparam ARB_MODE_ID_WIDTH              = (ARB_MODES_NUM == 1) ? 1 : $clog2(ARB_MODES_NUM),        // width of an ID of an arbitration mode
  localparam IN_INTERFACES_NUM              = 4,                               // number of supported input interfaces
  localparam IN_INTERFACE_ID_WIDTH          = (IN_INTERFACES_NUM == 1) ? 1 : $clog2(IN_INTERFACES_NUM) // width of an ID of an input interface
)(
  // clocks and resets:
  input logic                               clk,                               // clock
  input logic                               nreset,                            // asynchronous reset (active low)
  // processing control interface:
  input logic                               proc_req,                          // processing request
  input logic                               proc_req_in0_en,                   // input interface 0 - enable flag
  input logic       [ARB_MODE_ID_WIDTH-1:0] proc_req_in0_arb_mode_id,          // input interface 0 - arbitration mode ID
  input logic                               proc_req_in1_en,                   // input interface 1 - enable flag
  input logic       [ARB_MODE_ID_WIDTH-1:0] proc_req_in1_arb_mode_id,          // input interface 1 - arbitration mode ID
  input logic                               proc_req_in2_en,                   // input interface 2 - enable flag
  input logic       [ARB_MODE_ID_WIDTH-1:0] proc_req_in2_arb_mode_id,          // input interface 2 - arbitration mode ID
  output logic                              proc_ack,                          // processing acknowledgement
  // input interface 0:
  input logic                               in0_valid,                         // valid flag
  output logic                              in0_ready,                         // ready flag
  input logic              [DATA_WIDTH-1:0] in0_data,                          // data
  input logic                               in0_data_last,                     // indicator of last data in a frame
  // input interface 1:
  input logic                               in1_valid,                         // valid flag
  output logic                              in1_ready,                         // ready flag
  input logic              [DATA_WIDTH-1:0] in1_data,                          // data
  input logic                               in1_data_last,                     // indicator of last data in a frame
  // input interface 2:
  input logic                               in2_valid,                         // valid flag
  output logic                              in2_ready,                         // ready flag
  input logic              [DATA_WIDTH-1:0] in2_data,                          // data
  input logic                               in2_data_last,                     // indicator of last data in a frame
  // output interface:
  output logic                              out_valid,                         // valid flag
  input logic                               out_ready,                         // ready flag
  output logic             [DATA_WIDTH-1:0] out_data,                          // data
  output logic  [IN_INTERFACE_ID_WIDTH-1:0] out_data_source_id,                // source ID (indicator of an input interface from which the data is taken)
  output logic                              out_data_last                      // indicator of last data in a frame
);

  //===========================================================================
  // other local parameters
  //===========================================================================
  localparam FIFO_WIDTH                     = DATA_WIDTH + IN_INTERFACE_ID_WIDTH + 1;  // width of fifo data bus

  //===========================================================================
  // internal signals
  //===========================================================================

  //---------------------------------------------------------------------------
  // overall control logic
  //---------------------------------------------------------------------------
  logic                                     out_last_data_sent_c;
  //-----
  logic                                     in0_en_c;
  logic                                     in1_en_c;
  logic                                     in2_en_c;
  //-----
  logic             [ARB_MODE_ID_WIDTH-1:0] in0_arb_mode_id_en_c;
  logic             [ARB_MODE_ID_WIDTH-1:0] in1_arb_mode_id_en_c;
  logic             [ARB_MODE_ID_WIDTH-1:0] in2_arb_mode_id_en_c;
  //-----
  logic                                     first_cycle_of_proc_req_c;
  //-----
  logic proc_ack_c;

  //---------------------------------------------------------------------------
  // input interface 0 control logic
  //---------------------------------------------------------------------------
  logic                                     in0_ready_c;                       // ready flag of input interface 0
  //-----
  logic                                     in0_valid_c;                       // indicator of valid data from input interface 0 in an internal register - register
  //-----
  logic                    [DATA_WIDTH-1:0] in0_data_c;                        // internally registered data from input interface 0 - register
  logic                                     in0_data_last_c;                   // internally registered indicator of last data in a frame from input interface 0
  logic                                     arb_in0_transferring_c;            // indicator of arbitrating of a transfer from the input interface 0

  //---------------------------------------------------------------------------
  // input interface 1 control logic
  //---------------------------------------------------------------------------
  logic                                     in1_ready_c;                       // ready flag of input interface 1
  //-----
  logic                                     in1_valid_c;                       // indicator of valid data from input interface 1 in an internal register - register
  //-----
  logic                    [DATA_WIDTH-1:0] in1_data_c;                        // internally registered data from input interface 1 - register
  logic                                     in1_data_last_c;                   // internally registered indicator of last data in a frame from input interface 1
  logic                                     arb_in1_transferring_c;            // indicator of arbitrating of a transfer from the input interface 1

  //---------------------------------------------------------------------------
  // input interface 2 control logic
  //---------------------------------------------------------------------------
  logic                                     in2_ready_c;                       // ready flag of input interface 2
  //-----
  logic                                     in2_valid_c;                       // indicator of valid data from input interface 2 in an internal register - register
  //-----
  logic                    [DATA_WIDTH-1:0] in2_data_c;                        // internally registered data from input interface 2 - register
  logic                                     in2_data_last_c;                   // internally registered indicator of last data in a frame from input interface 2
  logic                                     arb_in2_transferring_c;            // indicator of arbitrating of a transfer from the input interface 2

  //---------------------------------------------------------------------------
  // arbitration control logic
  //---------------------------------------------------------------------------
  logic                  [DATA_WIDTH-1:0]   arb_data_c;
  logic       [IN_INTERFACE_ID_WIDTH-1:0]   arb_data_source_id_c;
  logic                                     arb_data_last_c;
  logic                                     arb_data_valid_c;
  logic                                     arb_data_ready_c;
  //---------------------------------------------------------------------------
  // FIFO control logic
  //---------------------------------------------------------------------------
  logic                  [FIFO_WIDTH-1:0]   fifo_wdata_c;                      // FIFO write data
  logic                                     fifo_we_c;                         // FIFO write enable flag
  logic                                     fifo_re_c;                         // FIFO read enable flag
  logic                    [FIFO_WIDTH-1:0] fifo_rdata_packed_c;
  //-----
  logic                                     fifo_full_c;                       // FIFO fullness indicator
  logic                                     fifo_empty_c;                      // FIFO emptiness indicator

  //---------------------------------------------------------------------------
  // output interface control logic
  //---------------------------------------------------------------------------
  logic                                     out_valid_c;
  logic                    [DATA_WIDTH-1:0] out_data_c;
  logic         [IN_INTERFACE_ID_WIDTH-1:0] out_data_source_id_c;
  logic                                     out_data_last_c;

  //===========================================================================
  // overall control logic
  //===========================================================================

  dut_processing_control #(
    .ARB_MODES_NUM                     (ARB_MODES_NUM)
  ) dut_processing_control_INST (
    .clk(clk),
    .nreset(nreset),
  
    .proc_req                          (proc_req),
    .proc_ack                          (proc_ack_c),
    .proc_req_in0_en                   (proc_req_in0_en),
    .proc_req_in0_arb_mode_id          (proc_req_in0_arb_mode_id),
    .proc_req_in1_en                   (proc_req_in1_en),
    .proc_req_in1_arb_mode_id          (proc_req_in1_arb_mode_id),
    .proc_req_in2_en                   (proc_req_in2_en),
    .proc_req_in2_arb_mode_id          (proc_req_in2_arb_mode_id),
  
    .out_last_data_sent                (out_last_data_sent_c),
    
    .in0_en                            (in0_en_c),
    .in1_en                            (in1_en_c),
    .in2_en                            (in2_en_c),

    .in0_arb_mode_id_en                (in0_arb_mode_id_en_c),
    .in1_arb_mode_id_en                (in1_arb_mode_id_en_c),
    .in2_arb_mode_id_en                (in2_arb_mode_id_en_c),
  
    .first_cycle_of_proc_req           (first_cycle_of_proc_req_c)
  
  );

  //===========================================================================
  // input interface 0 control instance
  //===========================================================================
  dut_input_channel_control #(
    .DATA_WIDTH                        (DATA_WIDTH)
  ) dut_input_channel_control_0_INST (
    .clk                               (clk),
    .nreset                            (nreset),
  
    .first_cycle_of_proc_req           (first_cycle_of_proc_req_c),
  
    // input interface:
    .in_en                             (in0_en_c),
    .in_valid                          (in0_valid),
    .in_ready                          (in0_ready_c),
    .in_data                           (in0_data),
    .in_data_last                      (in0_data_last),
  
    // arbiter interface:
    .in_valid_arb                      (in0_valid_c),
    .in_data_arb                       (in0_data_c),
    .in_data_last_arb                  (in0_data_last_c),
    .arb_in_transferring               (arb_in0_transferring_c)
  );

  //===========================================================================
  // input interface 1 control instance
  //===========================================================================
  dut_input_channel_control #(
    .DATA_WIDTH                        (DATA_WIDTH)
  ) dut_input_channel_control_1_INST (
    .clk                               (clk),
    .nreset                            (nreset),
  
    .first_cycle_of_proc_req           (first_cycle_of_proc_req_c),
  
    // input interface:
    .in_en                             (in1_en_c),
    .in_valid                          (in1_valid),
    .in_ready                          (in1_ready_c),
    .in_data                           (in1_data),
    .in_data_last                      (in1_data_last),
  
    // arbiter interface:
    .in_valid_arb                      (in1_valid_c),
    .in_data_arb                       (in1_data_c),
    .in_data_last_arb                  (in1_data_last_c),
    .arb_in_transferring               (arb_in1_transferring_c)
  );

  //===========================================================================
  // input interface 2 control instance
  //===========================================================================
  dut_input_channel_control #(
    .DATA_WIDTH                        (DATA_WIDTH)
  ) dut_input_channel_control_2_INST (
    .clk                               (clk),
    .nreset                            (nreset),
  
    .first_cycle_of_proc_req           (first_cycle_of_proc_req_c),
  
    // input interface:
    .in_en                             (in2_en_c),
    .in_valid                          (in2_valid),
    .in_ready                          (in2_ready_c),
    .in_data                           (in2_data),
    .in_data_last                      (in2_data_last),
  
    // arbiter interface:
    .in_valid_arb                      (in2_valid_c),
    .in_data_arb                       (in2_data_c),
    .in_data_last_arb                  (in2_data_last_c),
    .arb_in_transferring               (arb_in2_transferring_c)
  );

  //===========================================================================
  // arbiter instance
  //===========================================================================

  dut_arbiter #(
    .DATA_WIDTH                        (DATA_WIDTH),
    .IN_INTERFACE_ID_WIDTH             (IN_INTERFACE_ID_WIDTH),
    .ARB_MODES_NUM                     (ARB_MODES_NUM)
  ) dut_arbiter_INST (
    // clocks and resets
    .clk                               (clk),
    .nreset                            (nreset),
    
    // indicator of first cycle of processing, acts as a soft reset
    .first_cycle_of_proc_req           (first_cycle_of_proc_req_c),

    // channel 0 interface
    .in0_en                            (in0_en_c),
    .in0_arb_mode_id_en                (in0_arb_mode_id_en_c),
    .in0_valid                         (in0_valid_c),
    .in0_data                          (in0_data_c),
    .in0_data_last                     (in0_data_last_c),
    .arb_in0_transferring              (arb_in0_transferring_c),

    // channel 1 interface
    .in1_en                            (in1_en_c),
    .in1_arb_mode_id_en                (in1_arb_mode_id_en_c),
    .in1_valid                         (in1_valid_c),
    .in1_data                          (in1_data_c),
    .in1_data_last                     (in1_data_last_c),
    .arb_in1_transferring              (arb_in1_transferring_c),

    // channel 2 interface
    .in2_en                            (in2_en_c),
    .in2_arb_mode_id_en                (in2_arb_mode_id_en_c),
    .in2_valid                         (in2_valid_c),
    .in2_data                          (in2_data_c),
    .in2_data_last                     (in2_data_last_c),
    .arb_in2_transferring              (arb_in2_transferring_c),

    // arbiter output interface
    .arb_data                          (arb_data_c),
    .arb_data_source_id                (arb_data_source_id_c),
    .arb_data_last                     (arb_data_last_c),
    .arb_data_valid                    (arb_data_valid_c),
    .arb_data_ready                    (arb_data_ready_c)
  );

  //===========================================================================
  // math wrapper instance
  //===========================================================================
  dut_math_wrapper #(
    // configurable parameters:
    .DATA_WIDTH(DATA_WIDTH),
    .IN_INTERFACE_ID_WIDTH(IN_INTERFACE_ID_WIDTH)
  ) math_wrapper_INST (
    // clocks and resets:
    .clk                               (clk),
    .nreset                            (nreset),

    .in_data                           (arb_data_c),
    .in_data_source_id                 (arb_data_source_id_c),
    .in_data_last                      (arb_data_last_c),
    .in_data_valid                     (arb_data_valid_c),
    .in_data_ready                     (arb_data_ready_c),

    //output interface:
    .fifo_data                         (fifo_wdata_c),
    .fifo_we                           (fifo_we_c),
    .fifo_full                         (fifo_full_c)
  );

  //===========================================================================
  // FIFO instance
  //===========================================================================

  dut_fifo #(
    .FIFO_HEIGHT                       (FIFO_HEIGHT),
    .FIFO_WIDTH                        (FIFO_WIDTH)
  ) dut_fifo_INST (
    .clk                               (clk),
    .nreset                            (nreset),
    .soft_reset_ptrs                   (first_cycle_of_proc_req_c),

    .fifo_we                           (fifo_we_c),
    .fifo_wdata                        (fifo_wdata_c),
    .fifo_full                         (fifo_full_c),
    
    .fifo_re                           (fifo_re_c),
    .fifo_rdata                        (fifo_rdata_packed_c),
    .fifo_empty                        (fifo_empty_c)
    );


  //===========================================================================
  // output interface control logic
  //===========================================================================

    dut_output_control #(
    .DATA_WIDTH                        (DATA_WIDTH), 
    .IN_INTERFACE_ID_WIDTH             (IN_INTERFACE_ID_WIDTH)
  ) dut_output_control_INST (
    .clk                               (clk),
    .nreset                            (nreset),

    .first_cycle_of_proc_req           (first_cycle_of_proc_req_c),
    .fifo_empty                        (fifo_empty_c),
    .out_ready                         (out_ready),
    .fifo_out_data_packed              (fifo_rdata_packed_c),
    .fifo_re                           (fifo_re_c),

    .out_valid                         (out_valid_c),
    .out_data                          (out_data_c),
    .out_data_source_id                (out_data_source_id_c),
    .out_data_last                     (out_data_last_c),
    .out_last_data_sent                (out_last_data_sent_c)              // indicator that last output data has been sent out in a given frame - register
  );

  //===========================================================================
  // output assignments
  //===========================================================================

  //---------------------------------------------------------------------------
  // outputs of the processing control interface
  //---------------------------------------------------------------------------
  always_comb proc_ack           = proc_ack_c;

  //---------------------------------------------------------------------------
  // outputs of the input interface 0
  //---------------------------------------------------------------------------
  always_comb in0_ready          = in0_ready_c;

  //---------------------------------------------------------------------------
  // outputs of the input interface 1
  //---------------------------------------------------------------------------
  always_comb in1_ready          = in1_ready_c;

  //---------------------------------------------------------------------------
  // outputs of the input interface 2
  //---------------------------------------------------------------------------
  always_comb in2_ready          = in2_ready_c;

  //---------------------------------------------------------------------------
  // outputs of the output interface
  //---------------------------------------------------------------------------
  always_comb out_valid          = out_valid_c;
  always_comb out_data           = out_data_c;
  always_comb out_data_source_id = out_data_source_id_c;
  always_comb out_data_last      = out_data_last_c;

endmodule
