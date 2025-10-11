interface apb_interface #(
    parameter ADDR_WIDTH = 32, DATA_WIDTH = 32
) (
    input logic PCLK,   // For future Async AHB to APB Bridge
    input logic PRESETn
);

    // Signals
    logic [ADDR_WIDTH-1:0] PADDR;
    logic                  PSEL;
    logic                  PENABLE;
    logic                  PWRITE;
    logic [DATA_WIDTH-1:0] PWDATA;
    logic [DATA_WIDTH-1:0] PRDATA;

    // Modports
    modport master (
        output PADDR, PSEL, PENABLE, PWRITE, PWDATA,
        input  PRDATA
    );

    modport slave (
        input  PADDR, PSEL, PENABLE, PWRITE, PWDATA,
        output PRDATA
    );

endinterface
