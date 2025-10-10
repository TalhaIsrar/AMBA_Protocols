module ahb_to_apb_bridge #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    // ---------- AHB Slave Signals ---------- 
    input logic                     HCLK,
    input logic                     HRESETn,
    input logic                     HSEL,
    input logic  [ADDR_WIDTH - 1:0] HADDR,
    input logic  [1:0]              HTRANS,
    input logic                     HWRITE,
    input logic  [DATA_WIDTH - 1:0] HWDATA,

    output logic [DATA_WIDTH - 1:0] HRDATA,
    output logic [1:0]              HRESP,
    output logic                    HREADY,

    // ---------- APB Master Signals ---------
    input logic  [DATA_WIDTH - 1:0] PRDATA,
    
    output logic                    PSEL,
    output logic                    PENABLE,
    output logic [ADDR_WIDTH - 1:0] PADDR,
    output logic                    PWRITE,
    output logic [DATA_WIDTH - 1:0] PWDATA,
)



endmodule;