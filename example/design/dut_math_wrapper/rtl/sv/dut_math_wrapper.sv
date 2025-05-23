module dut_math_wrapper #(
  // configurable parameters:
  parameter DATA_WIDTH = 'x,
  parameter IN_INTERFACE_ID_WIDTH = 'x,
  // multiplier is fixed at 18 bit operands
  localparam MULTIPLICAND_WIDTH  = 18,
  localparam PRODUCT_WIDTH = 36,
  localparam FIFO_WIDTH = DATA_WIDTH + IN_INTERFACE_ID_WIDTH + 1
) (
  // clocks and resets:
  input logic                               clk,                               // clock
  input logic                               nreset,                            // asynchronous reset (active low)

  input logic             [DATA_WIDTH-1:0] in_data,
  input logic  [IN_INTERFACE_ID_WIDTH-1:0] in_data_source_id,
  input logic                              in_data_last,
  input logic                              in_data_valid,
  output logic                             in_data_ready,

  //output interface:
  output logic            [FIFO_WIDTH-1:0] fifo_data,
  output logic                             fifo_we,
  input  logic                             fifo_full
);


  //===========================================================================
  // internal signals
  //===========================================================================
  logic                                     new_data_nxt_c;
  logic                                     new_data_r;
  logic                                     unconsumed_data_nxt_c;
  logic                                     unconsumed_data_r;
  //-----
  logic            [MULTIPLICAND_WIDTH-1:0] in_a_c;
  logic            [MULTIPLICAND_WIDTH-1:0] in_b_c;
  //-----
  logic                 [PRODUCT_WIDTH-1:0] prod_c;
  //-----
  logic                    [FIFO_WIDTH-1:0] fifo_in_data_packed_c;
  //-----
  logic                    [DATA_WIDTH-1:0] out_data_r;                        // arbitrated data
  logic                                     out_data_last_r;                   // indicator that arbitrated data is last data in a frame
  logic         [IN_INTERFACE_ID_WIDTH-1:0] out_data_source_id_r;              // arbitrated source (input interface) ID
  //-----
  logic                                     in_data_ready_c;
  logic                                     fifo_we_c;

  
  //===========================================================================
  // internal logic
  //===========================================================================

  always_comb in_a_c = in_data[MULTIPLICAND_WIDTH-1:0];
  always_comb in_b_c = in_data[(2*MULTIPLICAND_WIDTH)-1:MULTIPLICAND_WIDTH];
  
  //prod = a*b
  dut_multiplier_18x18_comb dut_multiplier_18x18_comb_inst (
  .a(in_a_c),
  .b(in_b_c),
  .result(prod_c)
  );

  // handshake logic 

  always_comb new_data_nxt_c = (in_data_valid && in_data_ready);
  always_comb unconsumed_data_nxt_c = (new_data_r && !fifo_we) ? 1'b1 :
                                      (fifo_we) ? 1'b0 : 
                                      unconsumed_data_r;

  always_ff @ (posedge clk or negedge nreset) begin
    if(!nreset) begin
      new_data_r <= 1'b0;
      unconsumed_data_r <= 1'b0;
    end else begin
      new_data_r <= new_data_nxt_c;
      unconsumed_data_r <= unconsumed_data_nxt_c;
    end
  end
  always_comb in_data_ready_c = !(unconsumed_data_r || unconsumed_data_nxt_c); //back pressure of ready signal
  always_comb fifo_we_c = (new_data_r || unconsumed_data_r) & !fifo_full;

  //flop output data if input hanshaking occured
  always_ff @ (posedge clk or negedge nreset) begin
      if(!nreset) begin
        out_data_r <= {DATA_WIDTH{1'b0}};
        out_data_source_id_r <= {IN_INTERFACE_ID_WIDTH{1'b0}};
        out_data_last_r <= 1'b0;
      end
      else if (in_data_valid && in_data_ready) begin
        out_data_r <= {{(DATA_WIDTH- PRODUCT_WIDTH){1'b0}},prod_c};
        out_data_source_id_r <= in_data_source_id;
        out_data_last_r <= in_data_last;
      end
      else begin
        //keep previous data
    end
  end

  //---------------------------------------------------------------------------
  // pack data, last indicator and source ID into one word 
  //---------------------------------------------------------------------------
  always_comb fifo_in_data_packed_c = {
    out_data_r,
    out_data_last_r,
    out_data_source_id_r
  };

  
  //===========================================================================
  // output assignments
  //===========================================================================
  
  always_comb in_data_ready = in_data_ready_c;

  always_comb fifo_data = fifo_in_data_packed_c;
  always_comb fifo_we = fifo_we_c;

endmodule