module ahb_to_apb_bridge #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    // ---------- AHB Slave Signals ---------- 
    input logic                     HCLK,
    input logic                     HRESETn,    // Active low reset
    input logic                     HSEL,
    input logic  [ADDR_WIDTH - 1:0] HADDR,
    input logic  [1:0]              HTRANS,     // IDLE, BUSY, SEQ, NONSEQ
    input logic                     HWRITE,     // 1 =  Write, 0 = Read
    input logic                     HREADY_IN,
    input logic  [DATA_WIDTH - 1:0] HWDATA,

    output logic [DATA_WIDTH - 1:0] HRDATA,
    output logic [1:0]              HRESP,      // generate OKAY response
    output logic                    HREADY_OUT,

    // ---------- APB Master Signals ---------
    input logic  [DATA_WIDTH - 1:0] PRDATA,

    output logic                    PSEL,       // High same time as PADDR
    output logic                    PENABLE,
    output logic [ADDR_WIDTH - 1:0] PADDR,
    output logic                    PWRITE,
    output logic [DATA_WIDTH - 1:0] PWDATA
);

    // State variable for state machine
    typedef enum logic [2:0]   {ST_IDLE     = 3'b000,
                                ST_READ     = 3'b001,
                                ST_RENABLE  = 3'b010,
                                ST_WENABLE  = 3'b011,
                                ST_WRITE    = 3'b100,
                                ST_WWAIT    = 3'b101,
                                ST_WRITEP   = 3'b110,
                                ST_WENABLE  = 3'b111} bridge_states;

    bridge_states current_state, next_state;

    // State Register
    always_ff @(posedge HCLK or negedge HRESETn) begin
        if (!HRESETn) begin
            current_state <= ST_IDLE;
        end else begin
            current_state <= next_state;
        end 
    end


endmodule