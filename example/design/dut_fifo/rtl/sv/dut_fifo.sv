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

module dut_fifo #(
  // configurable parameters:
  parameter FIFO_HEIGHT = 'x,
  parameter FIFO_WIDTH = 'x,

  // local parameters used in port definitions:
  localparam FIFO_DEPTH = (FIFO_HEIGHT == 1) ? 1 : $clog2(FIFO_HEIGHT) // width of the FIFO address bus
)(
  // clocks and resets
  input logic clk,
  input logic nreset,

  // reset pointers values
  input logic soft_reset_ptrs,

  // write interface
  input logic fifo_we,
  input logic[FIFO_WIDTH-1:0] fifo_wdata,
  output logic fifo_full,

  // read interface
  input logic fifo_re,
  output logic[FIFO_WIDTH-1:0] fifo_rdata,
  output logic fifo_empty
);

  // other local parameters
  localparam FIFO_HEIGHT_MIN_1              = FIFO_HEIGHT-1;                  // number of entries in the FIFO, decreased by one

  //===========================================================================
  // internal signals
  //===========================================================================

  logic                   [FIFO_HEIGHT-1:0] fifo_data_en_c;                    // enable flags for FIFO data registers
  logic                    [FIFO_WIDTH-1:0] fifo_data_r           [FIFO_HEIGHT-1:0]; // FIFO - data - registers
  logic                    [FIFO_WIDTH-1:0] fifo_data_nxt_c;                   // FIFO - data - registers
  //-----
  logic                                     fifo_wptr_en_c;                    // enable flag for the fifo_wptr_r register
  logic                [(FIFO_DEPTH+1)-1:0] fifo_wptr_nxt_c;                   // next state of the fifo_wptr_r register
  logic                [(FIFO_DEPTH+1)-1:0] fifo_wptr_r;                       // FIFO write pointer - register
  //-----
  logic                                     fifo_rptr_en_c;                    // enable flag for the fifo_rptr_r register
  logic                [(FIFO_DEPTH+1)-1:0] fifo_rptr_nxt_c;                   // next state of the fifo_rptr_r register
  logic                [(FIFO_DEPTH+1)-1:0] fifo_rptr_r;                       // FIFO read pointer - register
  //-----
  logic                [(FIFO_DEPTH+1)-1:0] fifo_level_c;                      // FIFO level - number of occupied entries in the FIFO
  logic                                     fifo_full_c;                       // FIFO fullness indicator
  logic                                     fifo_empty_c;                      // FIFO emptiness indicator
  logic                    [FIFO_WIDTH-1:0] fifo_rdata_c;
  //-----

  //===========================================================================
  // internal logic
  //===========================================================================

  //---------------------------------------------------------------------------
  // FIFO write pointer - register
  //---------------------------------------------------------------------------
  // register enable flag:
  always_comb fifo_wptr_en_c  = soft_reset_ptrs ||
                           fifo_we;
  // next state of the register:
  always_comb fifo_wptr_nxt_c = (soft_reset_ptrs) ?
                           // reset at the beginning of a frame:
                                 {(FIFO_DEPTH+1){1'b0}} :
                           (fifo_wptr_r[FIFO_DEPTH-1:0] == FIFO_HEIGHT_MIN_1[FIFO_DEPTH-1:0]) ?
                           // reset and MSB change after writing to a last address:
                                 {~fifo_wptr_r[FIFO_DEPTH],{FIFO_DEPTH{1'b0}}} :
                           // regular address incrementing:
                                 fifo_wptr_r + {{((FIFO_DEPTH+1)-1){1'b0}},1'b1};
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      fifo_wptr_r <= {(FIFO_DEPTH+1){1'b0}};
    else if (fifo_wptr_en_c)
      fifo_wptr_r <= fifo_wptr_nxt_c;
    end

  //---------------------------------------------------------------------------
  // FIFO read pointer - register
  //---------------------------------------------------------------------------
  // register enable flag:
  always_comb fifo_rptr_en_c  = soft_reset_ptrs ||
                           fifo_re;
  // next state of the register:
  always_comb fifo_rptr_nxt_c = (soft_reset_ptrs) ?
                           // reset at the beginning of a frame:
                                 {(FIFO_DEPTH+1){1'b0}} :
                           (fifo_rptr_r[FIFO_DEPTH-1:0] == FIFO_HEIGHT_MIN_1[FIFO_DEPTH-1:0]) ?
                           // reset and MSB change after reading from a last address:
                                 {~fifo_rptr_r[FIFO_DEPTH],{FIFO_DEPTH{1'b0}}} :
                           // regular address incrementing:
                                 fifo_rptr_r + {{((FIFO_DEPTH+1)-1){1'b0}},1'b1};
  // register:
  always_ff @(posedge clk or negedge nreset)
    begin
    if (!nreset)
      fifo_rptr_r <= {(FIFO_DEPTH+1){1'b0}};
    else if (fifo_rptr_en_c)
      fifo_rptr_r <= fifo_rptr_nxt_c;
    end

  //---------------------------------------------------------------------------
  // FIFO level - number of occupied entries in the FIFO
  //---------------------------------------------------------------------------
  always_comb
    begin
    fifo_level_c                 = {(FIFO_DEPTH+1){1'b0}};
    fifo_level_c[FIFO_DEPTH-1:0] = fifo_wptr_r[FIFO_DEPTH-1:0] - fifo_rptr_r[FIFO_DEPTH-1:0];
    fifo_level_c[FIFO_DEPTH]     = !(|fifo_level_c[FIFO_DEPTH-1:0]) &&
                                   (fifo_wptr_r[FIFO_DEPTH] ^ fifo_rptr_r[FIFO_DEPTH]);
    end

  //---------------------------------------------------------------------------
  // FIFO fullness indicator
  //---------------------------------------------------------------------------
  always_comb fifo_full_c = (fifo_level_c == FIFO_HEIGHT[(FIFO_DEPTH+1)-1:0]);

  //---------------------------------------------------------------------------
  // FIFO emptiness indicator
  //---------------------------------------------------------------------------
  always_comb fifo_empty_c = !(|fifo_level_c);

  //---------------------------------------------------------------------------
  // FIFO data - registers
  //---------------------------------------------------------------------------
  // registers enable flags:
  always_comb
    begin : fifo_data_en_c_proc
    integer entry_id_c;
    for (entry_id_c = 0; entry_id_c < FIFO_HEIGHT; entry_id_c = entry_id_c + 1)
      fifo_data_en_c[entry_id_c] = fifo_we &&
                                   (fifo_wptr_r[FIFO_DEPTH-1:0] == entry_id_c[FIFO_DEPTH-1:0]);
    end
  // next states of the registers:
  always_comb fifo_data_nxt_c           = fifo_wdata;
  // registers:
  always_ff @(posedge clk or negedge nreset)
    begin : fifo_data_r_proc
    integer entry_id_c;
    if (!nreset)
      for (entry_id_c = 0; entry_id_c < FIFO_HEIGHT; entry_id_c = entry_id_c + 1)
        begin
        fifo_data_r[entry_id_c]           <= {FIFO_WIDTH{1'b0}};
        end
    else
      for (entry_id_c = 0; entry_id_c < FIFO_HEIGHT; entry_id_c = entry_id_c + 1)
        if (fifo_data_en_c[entry_id_c])
          begin
          fifo_data_r[entry_id_c]           <= fifo_data_nxt_c;
          end
    end

    always_comb fifo_rdata_c = fifo_data_r[fifo_rptr_r[FIFO_DEPTH-1:0]];

  //===========================================================================
  // output assignments
  //===========================================================================
  always_comb fifo_full = fifo_full_c;
  always_comb fifo_empty = fifo_empty_c;
  always_comb fifo_rdata = fifo_rdata_c;


  //===========================================================================
  // internal properties
  //===========================================================================
  `ifdef ASSERTIONS_EN
  //---------------------------------------------------------------------------
  // FIFO is not written, when the FIFO is full
  //---------------------------------------------------------------------------
  property pr__fifo_not_written_when_full;
    @(posedge clk) disable iff (!nreset)
      (fifo_we)
        |->
      (!fifo_full);
  endproperty
  as__fifo_not_written_when_full : assert property(pr__fifo_not_written_when_full) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

  //---------------------------------------------------------------------------
  // FIFO is not read, when the FIFO is empty
  //---------------------------------------------------------------------------
  property pr__fifo_not_read_when_empty;
    @(posedge clk) disable iff (!nreset)
      (fifo_re)
        |->
      (!fifo_empty);
  endproperty
  as__fifo_not_read_when_empty : assert property(pr__fifo_not_read_when_empty) else $error("%t: ERROR: ASSERTION FAILURE: %m", $time);

`endif

endmodule