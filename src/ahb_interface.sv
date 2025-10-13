interface ahb_interface #(
    parameter ADDR_WIDTH = 32, DATA_WIDTH = 32
) (
    input logic HCLK, 
    input logic HRESETn
);

    // Signals
    logic                     HSEL;
    logic [ADDR_WIDTH-1:0]    HADDR;
    logic [1:0]               HTRANS;
    logic                     HWRITE;
    logic [DATA_WIDTH-1:0]    HWDATA;

    logic [DATA_WIDTH-1:0]    HRDATA;
    logic [1:0]               HRESP;
    logic                     HREADY_OUT;

    // Modports
    modport master (
        output HSEL, HADDR, HTRANS, HWRITE, HWDATA,
        input  HRDATA, HRESP, HREADY_OUT
    );

    modport slave (
        input  HSEL, HADDR, HTRANS, HWRITE, HWDATA,
        output HRDATA, HRESP, HREADY_OUT
    );

endinterface
