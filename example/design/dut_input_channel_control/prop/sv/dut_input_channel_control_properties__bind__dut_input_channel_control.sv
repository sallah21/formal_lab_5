`ifdef ASSERTIONS_EN

bind dut_input_channel_control dut_input_channel_control_properties #(
  .DATA_WIDTH              (DATA_WIDTH)
) dut_input_chanel_control_properties (
  .clk                     (clk),
  .nreset                  (nreset),
  .first_cycle_of_proc_req (first_cycle_of_proc_req),
  .in_en                   (in_en),
  .in_valid                (in_valid),
  .in_ready                (in_ready),
  .in_data                 (in_data),
  .in_data_last            (in_data_last),
  .in_valid_arb            (in_valid_arb),
  .in_data_arb             (in_data_arb),
  .in_data_last_arb        (in_data_last_arb),
  .arb_in_transferring     (arb_in_transferring)
);

`endif // ASSERTIONS_EN
