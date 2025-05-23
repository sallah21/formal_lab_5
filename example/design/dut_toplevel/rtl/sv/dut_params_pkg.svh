`ifndef DUT_PARAMS_PKG
`define DUT_PARAMS_PKG

package dut_params_pkg;

  parameter DATA_WIDTH             = 36;                                                       // number of bits in a data word
  parameter FIFO_HEIGHT            = 4;                                                        // number of entries in the FIFO

  parameter ARB_MODES_NUM          = 2;                                                        // number of supported arbitration modes
  parameter ARB_MODE_ID_WIDTH      = (ARB_MODES_NUM == 1) ? 1 : $clog2(ARB_MODES_NUM);         // width of an ID of an arbitration mode
  parameter IN_INTERFACES_NUM      = 4;                                                        // number of supported input interfaces
  parameter IN_INTERFACE_ID_WIDTH  = (IN_INTERFACES_NUM == 1) ? 1 : $clog2(IN_INTERFACES_NUM); // width of an ID of an input interface
  
  typedef struct packed {
    logic [IN_INTERFACES_NUM-1:0]                        proc_req_in_en;
    logic [IN_INTERFACES_NUM-1:0][ARB_MODE_ID_WIDTH-1:0] proc_req_arb_mode_id;
  } dut_proc_control_req_t;

  typedef struct packed {
    logic [DATA_WIDTH-1:0]            data_in;
    logic                             data_last;
  } dut_input_data_t;

  typedef struct packed {
    logic [DATA_WIDTH-1:0]            data_out;
    logic [IN_INTERFACE_ID_WIDTH-1:0] data_source_id;
    logic                             data_last;
  } dut_output_data_t;

endpackage

`endif