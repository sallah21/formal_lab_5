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

module dut_toplevel_interface_properties #(
  // configurable parameters:
  parameter DATA_WIDTH                      = 8,                              // number of bits in a data word
  parameter FIFO_HEIGHT                     = 4,                               // number of entries in the FIFO
  // local parameters used in port definitions:
  localparam ARB_MODES_NUM                  = 2,                               // number of supported arbitration modes
  localparam ARB_MODE_ID_WIDTH              = (ARB_MODES_NUM == 1) ? 1 : $clog2(ARB_MODES_NUM),        // width of an ID of an arbitration mode
  localparam IN_INTERFACES_NUM              = 3,                               // number of supported input interfaces
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
  input logic                               proc_ack,                          // processing acknowledgement
  // input interface 0:
  input logic                               in0_valid,                         // valid flag
  input logic                               in0_ready,                         // ready flag
  input logic              [DATA_WIDTH-1:0] in0_data,                          // data
  input logic                               in0_data_last,                     // indicator of last data in a frame
  // input interface 1:
  input logic                               in1_valid,                         // valid flag
  input logic                               in1_ready,                         // ready flag
  input logic              [DATA_WIDTH-1:0] in1_data,                          // data
  input logic                               in1_data_last,                     // indicator of last data in a frame
  // input interface 2:
  input logic                               in2_valid,                         // valid flag
  input logic                               in2_ready,                         // ready flag
  input logic              [DATA_WIDTH-1:0] in2_data,                          // data
  input logic                               in2_data_last,                     // indicator of last data in a frame
  // output interface:
  input logic                               out_valid,                         // valid flag
  input logic                               out_ready,                         // ready flag
  input logic              [DATA_WIDTH-1:0] out_data,                          // data
  input logic   [IN_INTERFACE_ID_WIDTH-1:0] out_data_source_id,                // source ID (indicator of an input interface from which the data is taken)
  input logic                               out_data_last                      // indicator of last data in a frame
);

  //===========================================================================
  // other local parameters
  //===========================================================================
  localparam SINGLE_FRAME_EN                = 1;                               // when 1, then only one frame is verified; when 0, number of frames is unconstrained
  localparam SCOREBOARD_EN                  = 0;                               // when 1, output data is checked if it is the same as corresponding input data; when 0, this check is disabled
  localparam MAX_IN_TRANSFERS_NUM           = 4;                               // maximum number of input transfers (per each input interface) per frame
  localparam MAX_IN_TRANSFERS_NUM_MIN_1     = MAX_IN_TRANSFERS_NUM-1;          // maximum number of input transfers (per each input interface) per frame, decreased by one
  localparam IN_TRANSFER_ID_WIDTH           = (MAX_IN_TRANSFERS_NUM == 1) ? 1 : $clog2(MAX_IN_TRANSFERS_NUM); // width of an input transfers ID
  localparam IN_INTERFACES_NUM_MIN_1        = IN_INTERFACES_NUM-1;             // number of supported input interfaces, decreased by one

  //===========================================================================
  // internal signals
  //===========================================================================

  //---------------------------------------------------------------------------
  // subsidiary logic
  //---------------------------------------------------------------------------
  logic                                abv_time_after_cycle_after_rst_nxt_c;   // next state of the abv_time_after_cycle_after_rst_r register
  logic                                abv_time_after_cycle_after_rst_r;       // indicator of time after cycle after reset - register
  //-----
  logic                                abv_first_cycle_after_rst_c;            // indicator of first cycle after reset
  //-----
  logic                                abv_any_frame_completed_en_c;           // enable flag for the abv_any_frame_completed_r register
  logic                                abv_any_frame_completed_nxt_c;          // next state of the abv_any_frame_completed_r register
  logic                                abv_any_frame_completed_r;              // indicator that any frame has been completed - register
  //-----
  logic                                abv_in0_transfers_cnt_en_c;             // enable flag for the abv_in0_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_in0_transfers_cnt_nxt_c;            // next state of the abv_in0_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_in0_transfers_cnt_r;                // counter of input interface 0 transfers in a frame - register
  //-----
  logic                                abv_in1_transfers_cnt_en_c;             // enable flag for the abv_in1_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_in1_transfers_cnt_nxt_c;            // next state of the abv_in1_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_in1_transfers_cnt_r;                // counter of input interface 1 transfers in a frame - register
  //-----
  logic                                abv_in2_transfers_cnt_en_c;             // enable flag for the abv_in2_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_in2_transfers_cnt_nxt_c;            // next state of the abv_in2_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_in2_transfers_cnt_r;                // counter of input interface 2 transfers in a frame - register
  //-----
  logic                                abv_out0_transfers_cnt_en_c;            // enable flag for the abv_out0_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_out0_transfers_cnt_nxt_c;           // next state of the abv_out0_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_out0_transfers_cnt_r;               // counter of output interface transfers with source ID = 0 in a frame - register
  //-----
  logic                                abv_out1_transfers_cnt_en_c;            // enable flag for the abv_out1_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_out1_transfers_cnt_nxt_c;           // next state of the abv_out1_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_out1_transfers_cnt_r;               // counter of output interface transfers with source ID = 1 in a frame - register
  //-----
  logic                                abv_out2_transfers_cnt_en_c;            // enable flag for the abv_out2_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_out2_transfers_cnt_nxt_c;           // next state of the abv_out2_transfers_cnt_r register
  logic [(IN_TRANSFER_ID_WIDTH+1)-1:0] abv_out2_transfers_cnt_r;               // counter of output interface transfers with source ID = 2 in a frame - register
  //-----
  logic                                abv_in0_data_last_sent_en_c;            // enable flag for the abv_ino_data_last_sent_r register
  logic                                abv_in0_data_last_sent_nxt_c;           // next state of the abv_ino_data_last_sent_r register
  logic                                abv_in0_data_last_sent_r;               // indicator that last input data (form the input interface 0) has been already sent in a current frame - register
  //-----
  logic                                abv_in1_data_last_sent_en_c;            // enable flag for the abv_in1_data_last_sent_r register
  logic                                abv_in1_data_last_sent_nxt_c;           // next state of the abv_in1_data_last_sent_r register
  logic                                abv_in1_data_last_sent_r;               // indicator that last input data (form the input interface 1) has been already sent in a current frame - register
  //-----
  logic                                abv_in2_data_last_sent_en_c;            // enable flag for the abv_in2_data_last_sent_r register
  logic                                abv_in2_data_last_sent_nxt_c;           // next state of the abv_in2_data_last_sent_r register
  logic                                abv_in2_data_last_sent_r;               // indicator that last input data (form the input interface 2) has been already sent in a current frame - register
  //-----
  logic                                abv_out_data_last_sent_en_c;            // enable flag for the abv_out_data_last_sent_r register
  logic                                abv_out_data_last_sent_nxt_c;           // next state of the abv_out_data_last_sent_r register
  logic                                abv_out_data_last_sent_r;               // indicator that last output data has been already sent in a current frame - register
  //-----
  logic     [MAX_IN_TRANSFERS_NUM-1:0] abv_in0_data_en_c;                      // enable flags for the abv_in0_data_r registers
  logic               [DATA_WIDTH-1:0] abv_in0_data_nxt_c;                     // next state of the abv_in0_data_r registers
  logic               [DATA_WIDTH-1:0] abv_in0_data_r [MAX_IN_TRANSFERS_NUM-1:0]; // all input interface 0 data transferred in a current frame - registers
  //-----
  logic     [MAX_IN_TRANSFERS_NUM-1:0] abv_in1_data_en_c;                      // enable flags for the abv_in1_data_r registers
  logic               [DATA_WIDTH-1:0] abv_in1_data_nxt_c;                     // next state of the abv_in1_data_r registers
  logic               [DATA_WIDTH-1:0] abv_in1_data_r [MAX_IN_TRANSFERS_NUM-1:0]; // all input interface 1 data transferred in a current frame - registers
  //-----
  logic     [MAX_IN_TRANSFERS_NUM-1:0] abv_in2_data_en_c;                      // enable flags for the abv_in2_data_r registers
  logic               [DATA_WIDTH-1:0] abv_in2_data_nxt_c;                     // next state of the abv_in2_data_r registers
  logic               [DATA_WIDTH-1:0] abv_in2_data_r [MAX_IN_TRANSFERS_NUM-1:0]; // all input interface 2 data transferred in a current frame - registers
  //-----
  logic                                abv_in0_valid_in_prev_cycle_nxt_c;      // next state of the in0_valid_in_prev_cycle_r register
  logic                                abv_in0_ready_in_prev_cycle_nxt_c;      // next state of the in0_ready_in_prev_cycle_r register
  logic                                abv_in1_valid_in_prev_cycle_nxt_c;      // next state of the in1_valid_in_prev_cycle_r register
  logic                                abv_in1_ready_in_prev_cycle_nxt_c;      // next state of the in1_ready_in_prev_cycle_r register
  logic                                abv_in2_valid_in_prev_cycle_nxt_c;      // next state of the in2_valid_in_prev_cycle_r register
  logic                                abv_in2_ready_in_prev_cycle_nxt_c;      // next state of the in2_ready_in_prev_cycle_r register
  logic                                abv_in0_valid_in_prev_cycle_r;          // state of the in0_valid signal in a previous cycle - register
  logic                                abv_in0_ready_in_prev_cycle_r;          // state of the in0_ready signal in a previous cycle - register
  logic                                abv_in1_valid_in_prev_cycle_r;          // state of the in1_valid signal in a previous cycle - register
  logic                                abv_in1_ready_in_prev_cycle_r;          // state of the in1_ready signal in a previous cycle - register
  logic                                abv_in2_valid_in_prev_cycle_r;          // state of the in2_valid signal in a previous cycle - register
  logic                                abv_in2_ready_in_prev_cycle_r;          // state of the in2_ready signal in a previous cycle - register
  //-----
  logic                                abv_in_data_sent_recently_en_c;         // enable flag for registers with indicators that data from particular input interfaces has been transferred recently
  logic                                abv_in0_data_sent_recently_nxt_c;       // next state of the abv_in0_data_sent_recently_r register
  logic                                abv_in1_data_sent_recently_nxt_c;       // next state of the abv_in1_data_sent_recently_r register
  logic                                abv_in2_data_sent_recently_nxt_c;       // next state of the abv_in2_data_sent_recently_r register
  logic                                abv_in0_data_sent_recently_r;           // indicators that data from input interface 0 has been transferred recently (taking transfers from all input interfaces into account) - register
  logic                                abv_in1_data_sent_recently_r;           // indicators that data from input interface 1 has been transferred recently (taking transfers from all input interfaces into account) - register
  logic                                abv_in2_data_sent_recently_r;           // indicators that data from input interface 2 has been transferred recently (taking transfers from all input interfaces into account) - register

  //===========================================================================
  // subsidiary logic
  //===========================================================================

  //---------------------------------------------------------------------------
  // indicator of time after cycle after reset - register
  //---------------------------------------------------------------------------
  // next state of the register:
  assign abv_time_after_cycle_after_rst_nxt_c = 1'b1;
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_time_after_cycle_after_rst_r <= 1'b0;
    else
      abv_time_after_cycle_after_rst_r <= abv_time_after_cycle_after_rst_nxt_c;
    end

  //---------------------------------------------------------------------------
  // indicator of a first cycle after reset
  //---------------------------------------------------------------------------
  assign abv_first_cycle_after_rst_c = nreset &&
                                       !abv_time_after_cycle_after_rst_r;

  //---------------------------------------------------------------------------
  // indicator that any frame has been completed - register
  //---------------------------------------------------------------------------
  // register enable flag:
  assign abv_any_frame_completed_en_c  = proc_ack;
  // next state of the register:
  assign abv_any_frame_completed_nxt_c = 1'b1;
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_any_frame_completed_r <= 1'b0;
    else if (abv_any_frame_completed_en_c)
      abv_any_frame_completed_r <= abv_any_frame_completed_nxt_c;
    end

  //---------------------------------------------------------------------------
  // counter of input interface 0 transfers in a frame - register
  //---------------------------------------------------------------------------
  // register enable flag:
  assign abv_in0_transfers_cnt_en_c  = proc_ack ||
                                       (in0_valid &&
                                        in0_ready);
  // next state of the register:
  assign abv_in0_transfers_cnt_nxt_c = (proc_ack) ?
                                       // counter reset:
                                             {(IN_TRANSFER_ID_WIDTH+1){1'b0}} :
                                       // counter incrementing:
                                             abv_in0_transfers_cnt_r + {{((IN_TRANSFER_ID_WIDTH+1)-1){1'b0}},1'b1};
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_in0_transfers_cnt_r <= {(IN_TRANSFER_ID_WIDTH+1){1'b0}};
    else if (abv_in0_transfers_cnt_en_c)
      abv_in0_transfers_cnt_r <= abv_in0_transfers_cnt_nxt_c;
    end

  //---------------------------------------------------------------------------
  // counter of input interface 1 transfers in a frame - register
  //---------------------------------------------------------------------------
  // register enable flag:
  assign abv_in1_transfers_cnt_en_c  = proc_ack ||
                                       (in1_valid &&
                                        in1_ready);
  // next state of the register:
  assign abv_in1_transfers_cnt_nxt_c = (proc_ack) ?
                                       // counter reset:
                                             {(IN_TRANSFER_ID_WIDTH+1){1'b0}} :
                                       // counter incrementing:
                                             abv_in1_transfers_cnt_r + {{((IN_TRANSFER_ID_WIDTH+1)-1){1'b0}},1'b1};
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_in1_transfers_cnt_r <= {(IN_TRANSFER_ID_WIDTH+1){1'b0}};
    else if (abv_in1_transfers_cnt_en_c)
      abv_in1_transfers_cnt_r <= abv_in1_transfers_cnt_nxt_c;
    end

  //---------------------------------------------------------------------------
  // counter of input interface 2 transfers in a frame - register
  //---------------------------------------------------------------------------
  // register enable flag:
  assign abv_in2_transfers_cnt_en_c  = proc_ack ||
                                       (in2_valid &&
                                        in2_ready);
  // next state of the register:
  assign abv_in2_transfers_cnt_nxt_c = (proc_ack) ?
                                       // counter reset:
                                             {(IN_TRANSFER_ID_WIDTH+1){1'b0}} :
                                       // counter incrementing:
                                             abv_in2_transfers_cnt_r + {{((IN_TRANSFER_ID_WIDTH+1)-1){1'b0}},1'b1};
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_in2_transfers_cnt_r <= {(IN_TRANSFER_ID_WIDTH+1){1'b0}};
    else if (abv_in2_transfers_cnt_en_c)
      abv_in2_transfers_cnt_r <= abv_in2_transfers_cnt_nxt_c;
    end

  //---------------------------------------------------------------------------
  // counter of output interface transfers with source ID = 0 in a frame -
  //   register
  //---------------------------------------------------------------------------
  // register enable flag:
  assign abv_out0_transfers_cnt_en_c  = proc_ack ||
                                        (out_valid &&
                                         out_ready &&
                                         (out_data_source_id == 2'b00));
  // next state of the register:
  assign abv_out0_transfers_cnt_nxt_c = (proc_ack) ?
                                       // counter reset:
                                             {(IN_TRANSFER_ID_WIDTH+1){1'b0}} :
                                       // counter incrementing:
                                             abv_out0_transfers_cnt_r + {{((IN_TRANSFER_ID_WIDTH+1)-1){1'b0}},1'b1};
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_out0_transfers_cnt_r <= {(IN_TRANSFER_ID_WIDTH+1){1'b0}};
    else if (abv_out0_transfers_cnt_en_c)
      abv_out0_transfers_cnt_r <= abv_out0_transfers_cnt_nxt_c;
    end

  //---------------------------------------------------------------------------
  // counter of output interface transfers with source ID = 1 in a frame -
  //   register
  //---------------------------------------------------------------------------
  // register enable flag:
  assign abv_out1_transfers_cnt_en_c  = proc_ack ||
                                        (out_valid &&
                                         out_ready &&
                                         (out_data_source_id == 2'b01));
  // next state of the register:
  assign abv_out1_transfers_cnt_nxt_c = (proc_ack) ?
                                       // counter reset:
                                             {(IN_TRANSFER_ID_WIDTH+1){1'b0}} :
                                       // counter incrementing:
                                             abv_out1_transfers_cnt_r + {{((IN_TRANSFER_ID_WIDTH+1)-1){1'b0}},1'b1};
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_out1_transfers_cnt_r <= {(IN_TRANSFER_ID_WIDTH+1){1'b0}};
    else if (abv_out1_transfers_cnt_en_c)
      abv_out1_transfers_cnt_r <= abv_out1_transfers_cnt_nxt_c;
    end

  //---------------------------------------------------------------------------
  // counter of output interface transfers with source ID = 2 in a frame -
  //   register
  //---------------------------------------------------------------------------
  // register enable flag:
  assign abv_out2_transfers_cnt_en_c  = proc_ack ||
                                        (out_valid &&
                                         out_ready &&
                                         (out_data_source_id == 2'b10));
  // next state of the register:
  assign abv_out2_transfers_cnt_nxt_c = (proc_ack) ?
                                       // counter reset:
                                             {(IN_TRANSFER_ID_WIDTH+1){1'b0}} :
                                       // counter incrementing:
                                             abv_out2_transfers_cnt_r + {{((IN_TRANSFER_ID_WIDTH+1)-1){1'b0}},1'b1};
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_out2_transfers_cnt_r <= {(IN_TRANSFER_ID_WIDTH+1){1'b0}};
    else if (abv_out2_transfers_cnt_en_c)
      abv_out2_transfers_cnt_r <= abv_out2_transfers_cnt_nxt_c;
    end

  //---------------------------------------------------------------------------
  // indicator that last input data (form the input interface 0) has been
  //   already sent in a current frame - register
  //---------------------------------------------------------------------------
  // this signal is not used when processing is being acknowledged; that is
  //   why, it may clear when the acknowledgement is high
  //-----------------------------------
  // register enable flag:
  assign abv_in0_data_last_sent_en_c  = proc_ack ||
                                        (in0_valid &&
                                         in0_ready &&
                                         in0_data_last);
  // next state of the register:
  assign abv_in0_data_last_sent_nxt_c = !proc_ack;
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_in0_data_last_sent_r <= 1'b0;
    else if (abv_in0_data_last_sent_en_c)
      abv_in0_data_last_sent_r <= abv_in0_data_last_sent_nxt_c;
    end

  //---------------------------------------------------------------------------
  // indicator that last input data (form the input interface 1) has been
  //   already sent in a current frame - register
  //---------------------------------------------------------------------------
  // this signal is not used when processing is being acknowledged; that is
  //   why, it may clear when the acknowledgement is high
  //-----------------------------------
  // register enable flag:
  assign abv_in1_data_last_sent_en_c  = proc_ack ||
                                        (in1_valid &&
                                         in1_ready &&
                                         in1_data_last);
  // next state of the register:
  assign abv_in1_data_last_sent_nxt_c = !proc_ack;
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_in1_data_last_sent_r <= 1'b0;
    else if (abv_in1_data_last_sent_en_c)
      abv_in1_data_last_sent_r <= abv_in1_data_last_sent_nxt_c;
    end

  //---------------------------------------------------------------------------
  // indicator that last input data (form the input interface 2) has been
  //   already sent in a current frame - register
  //---------------------------------------------------------------------------
  // this signal is not used when processing is being acknowledged; that is
  //   why, it may clear when the acknowledgement is high
  //-----------------------------------
  // register enable flag:
  assign abv_in2_data_last_sent_en_c  = proc_ack ||
                                        (in2_valid &&
                                         in2_ready &&
                                         in2_data_last);
  // next state of the register:
  assign abv_in2_data_last_sent_nxt_c = !proc_ack;
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_in2_data_last_sent_r <= 1'b0;
    else if (abv_in2_data_last_sent_en_c)
      abv_in2_data_last_sent_r <= abv_in2_data_last_sent_nxt_c;
    end

  //---------------------------------------------------------------------------
  // indicator that last output data has been already sent in a current
  //   frame - register
  //---------------------------------------------------------------------------
  // this signal is not used when processing is being acknowledged; that is
  //   why, it may clear when the acknowledgement is high
  //-----------------------------------
  // register enable flag:
  assign abv_out_data_last_sent_en_c  = proc_ack ||
                                        (out_valid &&
                                         out_ready &&
                                         out_data_last);
  // next state of the register:
  assign abv_out_data_last_sent_nxt_c = !proc_ack;
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      abv_out_data_last_sent_r <= 1'b0;
    else if (abv_out_data_last_sent_en_c)
      abv_out_data_last_sent_r <= abv_out_data_last_sent_nxt_c;
    end

  //---------------------------------------------------------------------------
  // all input interface 0 data transferred in a current frame - registers
  //---------------------------------------------------------------------------
  // registers enable flags:
  always_comb
    begin
    abv_in0_data_en_c                                                    = {MAX_IN_TRANSFERS_NUM{1'b0}};
    abv_in0_data_en_c[abv_in0_transfers_cnt_r[IN_TRANSFER_ID_WIDTH-1:0]] = in0_valid &&
                                                                           in0_ready;
    end
  // next state of the registers:
  assign abv_in0_data_nxt_c = in0_data;
  // registers:
  always_ff @(posedge clk or negedge nreset)
    begin : abv_in0_data_r_proc
    integer entry_id_c;
    if (!nreset)
      for (entry_id_c = 0; entry_id_c < MAX_IN_TRANSFERS_NUM; entry_id_c = entry_id_c + 1)
        abv_in0_data_r[entry_id_c] <= {DATA_WIDTH{1'b0}};
    else
      for (entry_id_c = 0; entry_id_c < MAX_IN_TRANSFERS_NUM; entry_id_c = entry_id_c + 1)
        if (abv_in0_data_en_c[entry_id_c])
          abv_in0_data_r[entry_id_c] <= abv_in0_data_nxt_c;
    end

  //---------------------------------------------------------------------------
  // all input interface 1 data transferred in a current frame - registers
  //---------------------------------------------------------------------------
  // registers enable flags:
  always_comb
    begin
    abv_in1_data_en_c                                                    = {MAX_IN_TRANSFERS_NUM{1'b0}};
    abv_in1_data_en_c[abv_in1_transfers_cnt_r[IN_TRANSFER_ID_WIDTH-1:0]] = in1_valid &&
                                                                           in1_ready;
    end
  // next state of the registers:
  assign abv_in1_data_nxt_c = in1_data;
  // registers:
  always_ff @(posedge clk or negedge nreset)
    begin : abv_in1_data_r_proc
    integer entry_id_c;
    if (!nreset)
      for (entry_id_c = 0; entry_id_c < MAX_IN_TRANSFERS_NUM; entry_id_c = entry_id_c + 1)
        abv_in1_data_r[entry_id_c] <= {DATA_WIDTH{1'b0}};
    else
      for (entry_id_c = 0; entry_id_c < MAX_IN_TRANSFERS_NUM; entry_id_c = entry_id_c + 1)
        if (abv_in1_data_en_c[entry_id_c])
          abv_in1_data_r[entry_id_c] <= abv_in1_data_nxt_c;
    end

  //---------------------------------------------------------------------------
  // all input interface 2 data transferred in a current frame - registers
  //---------------------------------------------------------------------------
  // registers enable flags:
  always_comb
    begin
    abv_in2_data_en_c                                                    = {MAX_IN_TRANSFERS_NUM{1'b0}};
    abv_in2_data_en_c[abv_in2_transfers_cnt_r[IN_TRANSFER_ID_WIDTH-1:0]] = in2_valid &&
                                                                           in2_ready;
    end
  // next state of the registers:
  assign abv_in2_data_nxt_c = in2_data;
  // registers:
  always_ff @(posedge clk or negedge nreset)
    begin : abv_in2_data_r_proc
    integer entry_id_c;
    if (!nreset)
      for (entry_id_c = 0; entry_id_c < MAX_IN_TRANSFERS_NUM; entry_id_c = entry_id_c + 1)
        abv_in2_data_r[entry_id_c] <= {DATA_WIDTH{1'b0}};
    else
      for (entry_id_c = 0; entry_id_c < MAX_IN_TRANSFERS_NUM; entry_id_c = entry_id_c + 1)
        if (abv_in2_data_en_c[entry_id_c])
          abv_in2_data_r[entry_id_c] <= abv_in2_data_nxt_c;
    end

  //---------------------------------------------------------------------------
  // states of input interfaces signals in a previous cycle - registers
  //---------------------------------------------------------------------------
  // next states of the registers:
  assign abv_in0_valid_in_prev_cycle_nxt_c = in0_valid;
  assign abv_in0_ready_in_prev_cycle_nxt_c = in0_ready;
  assign abv_in1_valid_in_prev_cycle_nxt_c = in1_valid;
  assign abv_in1_ready_in_prev_cycle_nxt_c = in1_ready;
  assign abv_in2_valid_in_prev_cycle_nxt_c = in2_valid;
  assign abv_in2_ready_in_prev_cycle_nxt_c = in2_ready;
  // registers:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      begin
      abv_in0_valid_in_prev_cycle_r <= 1'b0;
      abv_in0_ready_in_prev_cycle_r <= 1'b0;
      abv_in1_valid_in_prev_cycle_r <= 1'b0;
      abv_in1_ready_in_prev_cycle_r <= 1'b0;
      abv_in2_valid_in_prev_cycle_r <= 1'b0;
      abv_in2_ready_in_prev_cycle_r <= 1'b0;
      end
    else
      begin
      abv_in0_valid_in_prev_cycle_r <= abv_in0_valid_in_prev_cycle_nxt_c;
      abv_in0_ready_in_prev_cycle_r <= abv_in0_ready_in_prev_cycle_nxt_c;
      abv_in1_valid_in_prev_cycle_r <= abv_in1_valid_in_prev_cycle_nxt_c;
      abv_in1_ready_in_prev_cycle_r <= abv_in1_ready_in_prev_cycle_nxt_c;
      abv_in2_valid_in_prev_cycle_r <= abv_in2_valid_in_prev_cycle_nxt_c;
      abv_in2_ready_in_prev_cycle_r <= abv_in2_ready_in_prev_cycle_nxt_c;
      end
    end

  //---------------------------------------------------------------------------
  // indicators that data from particular input interfaces has been transferred
  //   recently (taking transfers from all input interfaces into account) -
  //   registers
  //---------------------------------------------------------------------------
  // these signals are used to analyze correctness of the arbitration scheme;
  //   in the RTL there is one registers stage before the arbiter; that is
  //   why first transfers from each input interface are ignored in these
  //   signals here (as they are not impacted by the arbitration)
  // also cycles proceeding cycles, when ready was high, but valid was low are
  //   ignored, as it means that these input registers are written in that
  //   cycles
  //-----------------------------------
  // registers enable flag:
  assign abv_in_data_sent_recently_en_c   = proc_ack ||
                                            (in0_valid &&
                                             in0_ready) ||
                                            (in1_valid &&
                                             in1_ready) ||
                                            (in2_valid &&
                                             in2_ready);
  assign abv_in0_data_sent_recently_nxt_c = !proc_ack &&
                                            in0_valid &&
                                            in0_ready &&
                                            !(abv_in0_ready_in_prev_cycle_r &&
                                              !abv_in0_valid_in_prev_cycle_r) &&
                                            (|abv_in0_transfers_cnt_r);
  assign abv_in1_data_sent_recently_nxt_c = !proc_ack &&
                                            in1_valid &&
                                            in1_ready &&
                                            !(abv_in1_ready_in_prev_cycle_r &&
                                              !abv_in1_valid_in_prev_cycle_r) &&
                                            (|abv_in1_transfers_cnt_r);
  assign abv_in2_data_sent_recently_nxt_c = !proc_ack &&
                                            in2_valid &&
                                            in2_ready &&
                                            !(abv_in2_ready_in_prev_cycle_r &&
                                              !abv_in2_valid_in_prev_cycle_r) &&
                                            (|abv_in2_transfers_cnt_r);
  // next states of the registers:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      begin
      abv_in0_data_sent_recently_r <= 1'b0;
      abv_in1_data_sent_recently_r <= 1'b0;
      abv_in2_data_sent_recently_r <= 1'b0;
      end
    else if (abv_in_data_sent_recently_en_c)
      begin
      abv_in0_data_sent_recently_r <= abv_in0_data_sent_recently_nxt_c;
      abv_in1_data_sent_recently_r <= abv_in1_data_sent_recently_nxt_c;
      abv_in2_data_sent_recently_r <= abv_in2_data_sent_recently_nxt_c;
      end
    end

  //===========================================================================
  // properties, assertions and assumptions for the processing control
  //   interface
  //===========================================================================

  //---------------------------------------------------------------------------
  // standard properties of a request/acknowledgment interface
  //---------------------------------------------------------------------------
  req_ack_interface_properties
    #(
      .INITIATOR_TO_TARGET_AS_ASSERTS            (0),
      .TARGET_TO_INITIATOR_AS_ASSERTS            (1),
      .REQ_DATA_WIDTH                            (IN_INTERFACES_NUM+IN_INTERFACES_NUM*ARB_MODE_ID_WIDTH),
      .ACK_DATA_WIDTH                            (1)
    )
    req_ack_properties_for_processing_control_interface
      (
        // clocks and resets:
        .clk                                     (clk),
        .nreset                                  (nreset),
        // request/acknowledgment interface:
        .req                                     (proc_req),
        .req_data                                ({proc_req_in0_en,
                                                   proc_req_in0_arb_mode_id,
                                                   proc_req_in1_en,
                                                   proc_req_in1_arb_mode_id,
                                                   proc_req_in2_en,
                                                   proc_req_in2_arb_mode_id}),
        .ack                                     (proc_ack),
        .ack_data                                (1'b0)
      );

  //---------------------------------------------------------------------------
  // no more than one processing request
  //---------------------------------------------------------------------------
  // this property is used only when the SINGLE_FRAME_EN parameter is set to 1
  //-----------------------------------
  property pr__no_more_than_one_proc_req;
    @(posedge clk) disable iff (!nreset)
      (abv_time_after_cycle_after_rst_r &&
       abv_any_frame_completed_r)
        |->
      (!($rose(proc_req)));
  endproperty
  generate
    if (SINGLE_FRAME_EN)
      begin: gb_am_no_more_than_one_proc_req
      am__no_more_than_one_proc_req : assume property(pr__no_more_than_one_proc_req);
      end
  endgenerate

  //---------------------------------------------------------------------------
  // processing request is ever high with an input interface enable flag high,
  //   when there is any valid data on that input interface
  //---------------------------------------------------------------------------
  property pr__proc_req_and_proc_req_in_en_ever_high_when_any_in_valid_high(proc_req_in_en,in_valid);
    @(posedge clk) disable iff (!nreset)
      ((abv_first_cycle_after_rst_c &&
        (!proc_req ||
         !proc_req_in_en) &&
        in_valid) ||
       (abv_time_after_cycle_after_rst_r &&
        $rose((!proc_req ||
               !proc_req_in_en) &&
              in_valid)))
        |-> ##1
      (##[0:$] (proc_req &&
                proc_req_in_en));
  endproperty
  am__proc_req_and_proc_req_in0_en_ever_high_when_any_in0_valid_high : assume property(pr__proc_req_and_proc_req_in_en_ever_high_when_any_in_valid_high(proc_req_in0_en,in0_valid));
  am__proc_req_and_proc_req_in1_en_ever_high_when_any_in1_valid_high : assume property(pr__proc_req_and_proc_req_in_en_ever_high_when_any_in_valid_high(proc_req_in1_en,in1_valid));
  am__proc_req_and_proc_req_in2_en_ever_high_when_any_in2_valid_high : assume property(pr__proc_req_and_proc_req_in_en_ever_high_when_any_in_valid_high(proc_req_in2_en,in2_valid));

  //---------------------------------------------------------------------------
  // arbitration mode ID is zero (in current version) when processing is
  //   requested
  //---------------------------------------------------------------------------
  property pr__proc_req_in_arb_mode_id_zero_when_proc_req_high(proc_req_in_arb_mode_id);
    @(posedge clk) disable iff (!nreset)
      (proc_req)
        |->
      (proc_req_in_arb_mode_id == {ARB_MODE_ID_WIDTH{1'b0}});
  endproperty
  am__proc_req_in0_arb_mode_id_zero_when_proc_req_high : assume property(pr__proc_req_in_arb_mode_id_zero_when_proc_req_high(proc_req_in0_arb_mode_id));
  am__proc_req_in1_arb_mode_id_zero_when_proc_req_high : assume property(pr__proc_req_in_arb_mode_id_zero_when_proc_req_high(proc_req_in1_arb_mode_id));
  am__proc_req_in2_arb_mode_id_zero_when_proc_req_high : assume property(pr__proc_req_in_arb_mode_id_zero_when_proc_req_high(proc_req_in2_arb_mode_id));

  //===========================================================================
  // properties, assertions and assumptions for the input interfaces
  //===========================================================================


  //---------------------------------------------------------------------------
  // maximum number of input interface transfers per frame is not exceeded
  //---------------------------------------------------------------------------
  property pr__in_transfers_num_not_exceeded(in_valid,in_data_last,abv_in_transfers_cnt);
    @(posedge clk) disable iff (!nreset)
      (in_valid &&
       (abv_in_transfers_cnt == MAX_IN_TRANSFERS_NUM_MIN_1[IN_TRANSFER_ID_WIDTH-1:0]))
        |->
      (in_data_last);
  endproperty
  am__in0_transfers_num_not_exceeded : assume property(pr__in_transfers_num_not_exceeded(in0_valid,in0_data_last,abv_in0_transfers_cnt_r));
  am__in1_transfers_num_not_exceeded : assume property(pr__in_transfers_num_not_exceeded(in1_valid,in1_data_last,abv_in1_transfers_cnt_r));
  am__in2_transfers_num_not_exceeded : assume property(pr__in_transfers_num_not_exceeded(in2_valid,in2_data_last,abv_in2_transfers_cnt_r));

  //---------------------------------------------------------------------------
  // input valid is ever high when processing is requested and a corresponding
  //   input interface is enabled
  //---------------------------------------------------------------------------
  property pr__in_valid_ever_high_when_proc_req_high_and_proc_in_en_high(proc_req_in_en,in_valid);
    @(posedge clk) disable iff (!nreset)
      ((abv_first_cycle_after_rst_c &&
        proc_req &&
        proc_req_in_en) ||
       (abv_time_after_cycle_after_rst_r &&
        $rose(proc_req &&
              proc_req_in_en)))
        |->
      (##[0:$] (in_valid));
  endproperty
  am__in0_valid_ever_high_when_proc_req_high_and_proc_in0_en_high : assume property(pr__in_valid_ever_high_when_proc_req_high_and_proc_in_en_high(proc_req_in0_en,in0_valid));
  am__in1_valid_ever_high_when_proc_req_high_and_proc_in0_en_high : assume property(pr__in_valid_ever_high_when_proc_req_high_and_proc_in_en_high(proc_req_in1_en,in1_valid));
  am__in2_valid_ever_high_when_proc_req_high_and_proc_in0_en_high : assume property(pr__in_valid_ever_high_when_proc_req_high_and_proc_in_en_high(proc_req_in2_en,in2_valid));

  //---------------------------------------------------------------------------
  // there is ever valid data with an indicator of last data high, if any data
  //   has been sent without that indicator being high
  //---------------------------------------------------------------------------
  property pr__data_last_ever_high_when_any_data_without_last_sent(valid,ready,data_last,abv_in0_transfers_cnt);
    @(posedge clk) disable iff (!nreset)
      ((abv_first_cycle_after_rst_c &&
        valid &&
        ready &&
        !data_last) ||
       (abv_time_after_cycle_after_rst_r &&
        $rose(|(abv_in0_transfers_cnt))))
        |->
      (##[0:$] (valid &&
                data_last));
  endproperty
  am__in0_data_last_ever_high_when_any_in0_data_without_last_sent : assume property(pr__data_last_ever_high_when_any_data_without_last_sent(in0_valid,in0_ready,in0_data_last,abv_in0_transfers_cnt_r));
  am__in1_data_last_ever_high_when_any_in1_data_without_last_sent : assume property(pr__data_last_ever_high_when_any_data_without_last_sent(in1_valid,in1_ready,in1_data_last,abv_in1_transfers_cnt_r));
  am__in2_data_last_ever_high_when_any_in2_data_without_last_sent : assume property(pr__data_last_ever_high_when_any_data_without_last_sent(in2_valid,in2_ready,in2_data_last,abv_in2_transfers_cnt_r));

  //---------------------------------------------------------------------------
  // input ready is high only when processing request is high
  //---------------------------------------------------------------------------
  property pr__in_ready_high_only_when_proc_req_high(in_ready);
    @(posedge clk) disable iff (!nreset)
      (in_ready)
        |->
      (proc_req);
  endproperty
  as__in0_ready_high_only_when_proc_req_high : assert property(pr__in_ready_high_only_when_proc_req_high(in0_ready)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__in1_ready_high_only_when_proc_req_high : assert property(pr__in_ready_high_only_when_proc_req_high(in1_ready)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__in2_ready_high_only_when_proc_req_high : assert property(pr__in_ready_high_only_when_proc_req_high(in2_ready)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // input ready is low only when processing acknowledgement is high
  //---------------------------------------------------------------------------
  property pr__in_ready_low_when_proc_ack_high(in_ready);
    @(posedge clk) disable iff (!nreset)
      (proc_ack)
        |->
      (!in_ready);
  endproperty
  as__in0_ready_low_when_proc_ack_high : assert property(pr__in_ready_low_when_proc_ack_high(in0_ready)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__in1_ready_low_when_proc_ack_high : assert property(pr__in_ready_low_when_proc_ack_high(in1_ready)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__in2_ready_low_when_proc_ack_high : assert property(pr__in_ready_low_when_proc_ack_high(in2_ready)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // input ready is high only when a corresponding input interface is enabled
  //---------------------------------------------------------------------------
  property pr__in_ready_high_only_when_proc_req_in_en_high(in_ready,proc_req_in_en);
    @(posedge clk) disable iff (!nreset)
      (in_ready)
        |->
      (proc_req_in_en);
  endproperty
  as__in0_ready_high_only_when_proc_req_in0_en_high : assert property(pr__in_ready_high_only_when_proc_req_in_en_high(in0_ready,proc_req_in0_en)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__in1_ready_high_only_when_proc_req_in1_en_high : assert property(pr__in_ready_high_only_when_proc_req_in_en_high(in1_ready,proc_req_in1_en)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__in2_ready_high_only_when_proc_req_in2_en_high : assert property(pr__in_ready_high_only_when_proc_req_in_en_high(in2_ready,proc_req_in2_en)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // input ready is low, if last input data has been already sent in a
  //   current frame
  //---------------------------------------------------------------------------
  property pr__in_ready_low_when_in_data_last_already_sent_in_frame(in_ready,abv_in_data_last_sent);
    @(posedge clk) disable iff (!nreset)
      (proc_req &&
       !proc_ack &&
       abv_in_data_last_sent)
        |->
      (!in_ready);
  endproperty
  as__in0_ready_low_when_in0_data_last_already_sent_in_frame : assert property(pr__in_ready_low_when_in_data_last_already_sent_in_frame(in0_ready,abv_in0_data_last_sent_r)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__in1_ready_low_when_in1_data_last_already_sent_in_frame : assert property(pr__in_ready_low_when_in_data_last_already_sent_in_frame(in1_ready,abv_in1_data_last_sent_r)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__in2_ready_low_when_in2_data_last_already_sent_in_frame : assert property(pr__in_ready_low_when_in_data_last_already_sent_in_frame(in2_ready,abv_in2_data_last_sent_r)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // input interfaces are arbitrated correctly (according to the round robin
  //   arbitration scheme)
  //---------------------------------------------------------------------------
  // in the RTL there is one registers stage before the arbiter; that is
  //   why first transfers from each input interface are ignored in this
  //   property (as they are not impacted by the arbitration)
  // also cycles proceeding cycles, when ready was high, but valid was low are
  //   ignored, as it means that these input registers are written in that
  //   cycles
  //-----------------------------------
  property pr__in_interfaces_arbitrated_correctly;
    @(posedge clk) disable iff (!nreset)
      ((in0_valid &&
        in0_ready &&
        !(abv_in0_ready_in_prev_cycle_r && !abv_in0_valid_in_prev_cycle_r) &&
        (|abv_in0_transfers_cnt_r)) ||
       (in1_valid &&
        in1_ready &&
        !(abv_in1_ready_in_prev_cycle_r && !abv_in1_valid_in_prev_cycle_r) &&
        (|abv_in1_transfers_cnt_r)) ||
       (in2_valid &&
        in2_ready &&
        !(abv_in2_ready_in_prev_cycle_r && !abv_in2_valid_in_prev_cycle_r) &&
        (|abv_in2_transfers_cnt_r)))
        |->
      ((!abv_in0_data_sent_recently_r && !abv_in1_data_sent_recently_r && !abv_in2_data_sent_recently_r) ||
       (in0_ready &&
        in0_valid &&
        (abv_in2_data_sent_recently_r ||
         (abv_in1_data_sent_recently_r && (in2_ready || !proc_req_in2_en || abv_in2_data_last_sent_r || !in2_valid)) ||
         (abv_in0_data_sent_recently_r && (in1_ready || !proc_req_in1_en || abv_in1_data_last_sent_r || !in1_valid) && (in2_ready || !proc_req_in2_en || abv_in2_data_last_sent_r || !in2_valid)))) ||
       (in1_ready &&
        in1_valid &&
        (abv_in0_data_sent_recently_r ||
         (abv_in2_data_sent_recently_r && (in0_ready || !proc_req_in0_en || abv_in0_data_last_sent_r || !in0_valid)) ||
         (abv_in1_data_sent_recently_r && (in2_ready || !proc_req_in2_en || abv_in2_data_last_sent_r || !in2_valid) && (in0_ready || !proc_req_in0_en || abv_in0_data_last_sent_r || !in0_valid)))) ||
       (in2_ready &&
        in2_valid &&
        (abv_in1_data_sent_recently_r ||
         (abv_in0_data_sent_recently_r && (in1_ready || !proc_req_in1_en || abv_in1_data_last_sent_r || !in1_valid)) ||
         (abv_in2_data_sent_recently_r && (in0_ready || !proc_req_in0_en || abv_in0_data_last_sent_r || !in0_valid) && (in1_ready || !proc_req_in1_en || abv_in1_data_last_sent_r || !in1_valid)))));
  endproperty
  as__in_interfaces_arbitrated_correctly : assert property(pr__in_interfaces_arbitrated_correctly) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);



  //---------------------------------------------------------------------------
  // output valid is high only when processing request is high
  //---------------------------------------------------------------------------
  property pr__out_valid_high_only_when_proc_req_high;
    @(posedge clk) disable iff (!nreset)
      (out_valid)
        |->
      (proc_req);
  endproperty
  as__out_valid_high_only_when_proc_req_high : assert property(pr__out_valid_high_only_when_proc_req_high) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // output valid is low only when processing acknowledgement is high
  //---------------------------------------------------------------------------
  property pr__out_valid_low_when_proc_ack_high;
    @(posedge clk) disable iff (!nreset)
      (proc_ack)
        |->
      (!out_valid);
  endproperty
  as__out_valid_low_when_proc_ack_high : assert property(pr__out_valid_low_when_proc_ack_high) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // output valid is low, if last output data has been already sent in a
  //   current frame
  //---------------------------------------------------------------------------
  property pr__out_valid_low_when_out_data_last_already_sent_in_frame;
    @(posedge clk) disable iff (!nreset)
      (proc_req &&
       !proc_ack &&
       abv_out_data_last_sent_r)
        |->
      (!out_valid);
  endproperty
  as__out_valid_low_when_out_data_last_already_sent_in_frame : assert property(pr__out_valid_low_when_out_data_last_already_sent_in_frame) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // output data last is sent in each frame (if any input interface is active)
  //---------------------------------------------------------------------------
  property pr__out_data_last_high_in_each_frame;
    @(posedge clk) disable iff (!nreset)
      ((proc_req_in0_en ||
        proc_req_in1_en ||
        proc_req_in2_en) &&
       ((abv_first_cycle_after_rst_c &&
         proc_ack) ||
        (abv_time_after_cycle_after_rst_r &&
         $rose(proc_ack))))
        |->
      (abv_out_data_last_sent_r);
  endproperty
  as__out_data_last_high_in_each_frame : assert property(pr__out_data_last_high_in_each_frame) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // output data source ID (indicator of an input interface from which the
  //   data is taken) is within a valid range
  //---------------------------------------------------------------------------
  property pr__out_data_source_id_within_valid_range;
    @(posedge clk) disable iff (!nreset)
      (out_valid)
        |->
      ({1'b0,out_data_source_id} <= {1'b0,IN_INTERFACES_NUM_MIN_1[IN_INTERFACE_ID_WIDTH-1:0]});
  endproperty
  as__out_data_source_id_within_valid_range : assert property(pr__out_data_source_id_within_valid_range) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // at the end of frame processing, number of output transfers with a given
  //   source ID is the same as number of input transfers from a corresponding
  //   input interface
  //---------------------------------------------------------------------------
  property pr__out_transfers_num_equal_to_in_transfers_num_at_the_end_of_frame(abv_out_transfers_cnt,abv_in_transfers_cnt);
    @(posedge clk) disable iff (!nreset)
      ((abv_first_cycle_after_rst_c &&
        proc_ack) ||
       (abv_time_after_cycle_after_rst_r &&
        $rose(proc_ack)))
        |->
      (abv_out_transfers_cnt == abv_in_transfers_cnt);
  endproperty
  as__out0_transfers_num_equal_to_in0_transfers_num_at_the_end_of_frame : assert property(pr__out_transfers_num_equal_to_in_transfers_num_at_the_end_of_frame(abv_out0_transfers_cnt_r,abv_in0_transfers_cnt_r)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__out1_transfers_num_equal_to_in1_transfers_num_at_the_end_of_frame : assert property(pr__out_transfers_num_equal_to_in_transfers_num_at_the_end_of_frame(abv_out1_transfers_cnt_r,abv_in1_transfers_cnt_r)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__out2_transfers_num_equal_to_in2_transfers_num_at_the_end_of_frame : assert property(pr__out_transfers_num_equal_to_in_transfers_num_at_the_end_of_frame(abv_out2_transfers_cnt_r,abv_in2_transfers_cnt_r)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

// no more sent than received

  //---------------------------------------------------------------------------
  // during frame processing, number of output transfers with a given source ID
  //   is not higher than number of input transfers from a corresponding
  //   input interface
  //---------------------------------------------------------------------------
  property pr__out_transfers_num_not_higher_than_in_transfers_num_during_frame(abv_out_transfers_cnt,abv_in_transfers_cnt);
    @(posedge clk) disable iff (!nreset)
      (proc_req)
        |->
      ({1'b0,abv_out_transfers_cnt} <= {1'b0,abv_in_transfers_cnt});
  endproperty
  as__out0_transfers_num_not_higher_than_in0_transfers_num_during_frame : assert property(pr__out_transfers_num_not_higher_than_in_transfers_num_during_frame(abv_out0_transfers_cnt_r,abv_in0_transfers_cnt_r)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__out1_transfers_num_not_higher_than_in1_transfers_num_during_frame : assert property(pr__out_transfers_num_not_higher_than_in_transfers_num_during_frame(abv_out1_transfers_cnt_r,abv_in1_transfers_cnt_r)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
  as__out2_transfers_num_not_higher_than_in2_transfers_num_during_frame : assert property(pr__out_transfers_num_not_higher_than_in_transfers_num_during_frame(abv_out2_transfers_cnt_r,abv_in2_transfers_cnt_r)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // output data sent with a given source ID is the same as input data received
  //   from a corresponding input interface
  //---------------------------------------------------------------------------
  // this property is used only when the SCOREBOARD_EN parameter is set to 1
  //-----------------------------------
  property pr__out_data_the_same_as_in_data(abv_in_data,abv_out_transfers_cnt,source_id);
    @(posedge clk) disable iff (!nreset)
      (out_valid &&
       out_ready &&
       (out_data_source_id == source_id))
        |->
      (out_data == abv_in_data[abv_out_transfers_cnt[IN_TRANSFER_ID_WIDTH-1:0]]);
  endproperty
  generate
    if (SCOREBOARD_EN)
      begin: gb_as_out_data_the_same_as_in_data
      as__out0_data_the_same_as_in0_data : assert property(pr__out_data_the_same_as_in_data(abv_in0_data_r,abv_out0_transfers_cnt_r,2'b00)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
      as__out1_data_the_same_as_in1_data : assert property(pr__out_data_the_same_as_in_data(abv_in1_data_r,abv_out1_transfers_cnt_r,2'b01)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
      as__out2_data_the_same_as_in2_data : assert property(pr__out_data_the_same_as_in_data(abv_in2_data_r,abv_out2_transfers_cnt_r,2'b10)) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);
      end
  endgenerate

endmodule

`endif // ASSERTIONS_EN
