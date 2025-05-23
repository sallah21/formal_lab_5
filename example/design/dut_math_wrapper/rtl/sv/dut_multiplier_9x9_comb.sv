module dut_multiplier_9x9_comb (
  input logic [8:0] a,
  input logic [8:0] b,
  output logic [17:0] product
);

 always_comb product = a*b;


endmodule
