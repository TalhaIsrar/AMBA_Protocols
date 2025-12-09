module ahb_to_apb_sva #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    input logic                     HCLK,
    input logic                     HRESETn,    // Active low reset
    input logic                     HSEL,
    input logic  [ADDR_WIDTH - 1:0] HADDR,
    input logic  [1:0]              HTRANS,     // IDLE, BUSY, SEQ, NONSEQ
    input logic                     HWRITE,     // 1 =  Write, 0 = Read
    input logic  [DATA_WIDTH - 1:0] HWDATA,

    input logic  [DATA_WIDTH - 1:0] HRDATA,
    input logic  [1:0]              HRESP,      // generate OKAY response
    input logic                     HREADY_OUT,

    // ---------- APB Master Signals ---------
    input logic  [DATA_WIDTH - 1:0] PRDATA,

    input logic                     PSEL,       // High same time as PADDR
    input logic                     PENABLE,
    input logic [ADDR_WIDTH - 1:0]  PADDR,
    input logic                     PWRITE,
    input logic [DATA_WIDTH - 1:0]  PWDATA
);

    // Ensure HRDATA = PRDATA
    property read_data_valid;
        @(posedge HCLK) disable iff (!HRESETn) 
        HRDATA == PRDATA;
    endproperty
    assert property (read_data_valid)
        else $error("SVA: HRDATA is not equal to PPRDATA");

    // PSEL is asserted when PENABLE is high
    property p_enable_has_p_select;
        @(posedge HCLK) disable iff (!HRESETn) 
        PENABLE |-> PSEL;
    endproperty
    assert property (p_enable_has_p_select)
        else $error("SVA: PSEL is asserted when PENABLE is high");


endmodule
