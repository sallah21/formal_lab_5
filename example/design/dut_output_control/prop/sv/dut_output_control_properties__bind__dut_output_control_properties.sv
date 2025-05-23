`ifdef ASSERTIONS_EN

  bind dut_output_control dut_output_control_properties #(
    .DATA_WIDTH              (DATA_WIDTH),
    .IN_INTERFACE_ID_WIDTH   (IN_INTERFACE_ID_WIDTH)
  ) dut_output_control__bind (
    .clk                     (clk),
    .nreset                  (nreset),
    .first_cycle_of_proc_req (first_cycle_of_proc_req),
    .fifo_empty              (fifo_empty),
    .out_ready               (out_ready),
    .fifo_out_data_packed    (fifo_out_data_packed),
    .fifo_re                 (fifo_re),
    .out_valid               (out_valid),
    .out_data                (out_data),
    .out_data_source_id      (out_data_source_id),
    .out_data_last           (out_data_last),
    .out_last_data_sent      (out_last_data_sent)
  );

`endif // ASSERTIONS_EN
