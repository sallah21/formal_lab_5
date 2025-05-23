module dut_multiplier_18x18_comb (
  input  logic[17:0] a,
  input  logic[17:0] b,
  output logic[35:0] result
);

  //===========================================================================
  // internal signals
  //===========================================================================

  logic [8:0] a_0;
  logic [8:0] a_1;
  logic [8:0] b_0;
  logic [8:0] b_1;

  logic [17:0] prd_a0_b0;
  logic [17:0] prd_a1_b0;
  logic [17:0] prd_a0_b1;
  logic [17:0] prd_a1_b1;

  logic [35:0] sum_of_prd;

  always_comb a_0 = a[8:0];
  always_comb a_1 = a[17:9];
  always_comb b_0 = b[8:0];
  always_comb b_1 = b[17:9];


  //===========================================================================
  // internal logic
  //===========================================================================
  dut_multiplier_9x9_comb mult_a0b0 (
    .a(a_0),
    .b(b_0),
    .product(prd_a0_b0)

  );

  dut_multiplier_9x9_comb mult_a1b0 (
    .a(a_1),
    .b(b_0),
    .product(prd_a1_b0)

  );

  dut_multiplier_9x9_comb mult_a0b1 (
    .a(a_0),
    .b(b_1),
    .product(prd_a0_b1)

  );

  dut_multiplier_9x9_comb mult_a1b1 (
    .a(a_1),
    .b(b_1),
    .product(prd_a1_b1)

  );

  always_comb sum_of_prd = {{18{1'b0}},prd_a0_b0} +
                      {{9{1'b0}},prd_a1_b0,{9{1'b0}}} +
                      {{9{1'b0}},prd_a0_b1,{9{1'b0}}} +
                      {prd_a1_b1,{18{1'b0}}};

  //===========================================================================
  // output assignments
  //===========================================================================
  always_comb result = sum_of_prd;

endmodule

