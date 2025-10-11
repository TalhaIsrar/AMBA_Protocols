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

    // Internal Signals
    logic valid;
    logic HwriteReg;

    logic [ADDR_WIDTH - 1:0] AddressReg;
    logic [DATA_WIDTH - 1:0] DataReg;

    // State variable for state machine
    typedef enum logic [2:0]   {ST_IDLE     = 3'b000,
                                ST_READ     = 3'b001,
                                ST_RENABLE  = 3'b010,
                                ST_WENABLE  = 3'b011,
                                ST_WRITE    = 3'b100,
                                ST_WWAIT    = 3'b101,
                                ST_WRITEP   = 3'b110,
                                ST_WENABLEP = 3'b111} bridge_states;

    bridge_states current_state, next_state;

    // State Register
    always_ff @(posedge HCLK or negedge HRESETn) begin
        if (!HRESETn) begin
            current_state <= ST_IDLE;
        end else begin
            current_state <= next_state;
        end 
    end

    // Next State Logic
    always_comb begin : NEXT_STATE_LOGIC
        case (current_state) 
            ST_IDLE: 
                next_state = valid ? (HWRITE ? ST_WWAIT : ST_READ) : ST_IDLE;
            
            ST_READ: 
                next_state = ST_RENABLE;
            
            ST_RENABLE: 
                next_state = valid ? (HWRITE ? ST_WWAIT : ST_READ) : ST_IDLE; 
            
            ST_WENABLE:
                next_state = valid ? (HWRITE ? ST_WWAIT : ST_READ) : ST_IDLE;

            ST_WRITE:
                next_state = valid ? ST_WENABLEP : ST_WENABLE;

            ST_WWAIT:
                next_state = valid ? ST_WRITEP : ST_WRITE;

            ST_WRITEP:
                next_state = ST_WENABLEP;

            ST_WENABLEP:
                next_state = HwriteReg ? (valid ? ST_WRITEP : ST_WRITE) : ST_READ;

            default: next_state = ST_IDLE
        endcase
    end

    // Output logic
    // Synchronous because according to spec, old values are needed
    always_ff @(posedge HCLK or negedge HRESETn) begin
        if (!HRESETn) begin
            HRDATA      <= 0;
            HRESP       <= 0;
            HREADY_OUT  <= 0;
            PSEL        <= 0;
            PENABLE     <= 0;
            PADDR       <= 0;
            PWRITE      <= 0;
            PWDATA      <= 0;
        end else begin
            case (current_state) 
                ST_IDLE: begin // Bridge is IDLE, no APB Transfer happening
                    PSEL        <= 1'b0;
                    PENABLE     <= 1'b0;
                    HREADY_OUT  <= 1'b1;
                end

                ST_READ: begin // Starts APB read transcation (SETUP Phase APB)
                    PADDR       <= HADDR;
                    PSEL        <= 1'b1;
                    PWRITE      <= 1'b0;
                    HREADY_OUT  <= 1'b0; // Insert Wait state
                    PENABLE     <= 1'b0;
                end
                
                ST_RENABLE: begin // Completes APB read transcation and allows Masters to continue (ACCESS Phase APB)
                    PENABLE     <= 1'b1;
                    HRDATA      <= PRDATA;
                    HREADY_OUT  <= 1'b1;
                end

                ST_WENABLE: begin // APB enable phase for write
                    PENABLE     <= 1'b1;
                    HREADY_OUT  <= 1'b1;
                end

                ST_WRITE: begin // APB Write address phase (SETUP Phase APB)
                    PADDR       <= AddressReg; // Get write address from buffer
                    AddressReg  <= HADDR;      // Buffer the address in case pipeline writes
                    HwriteReg   <= 1'b1;       // Buffer write req in case write after write
                    PWDATA      <= HWDATA;
                    PSEL        <= 1'b1;
                    PENABLE     <= 1'b0;
                    PWRITE      <= 1'b1;
                    HREADY_OUT  <= 1'b0;
                end

                ST_WWAIT: begin // Waits for AHB write data to become valid
                    AddressReg  <= HADDR;  // Buffer the address
                    HwriteReg   <= HWRITE; // Buffer write request
                    HREADY_OUT  <= 1'b0;   // Insert Wait state
                    PENABLE     <= 1'b0;
                end

                ST_WRITEP: begin // Pending WRITE Phase after current transfer
                    PADDR       <= AddressReg; // Get write address from buffer
                    AddressReg  <= HADDR;      // Buffer the address in case pipeline writes
                    HwriteReg   <= HWRITE;     // Buffer write req in case write after write
                    PWDATA      <= HWDATA;
                    PSEL        <= 1'b1;
                    PENABLE     <= 1'b0;
                    PWRITE      <= 1'b1;
                    HREADY_OUT  <= 1'b0;
                end

                ST_WENABLEP: begin // APB enable phase for write (ACCESS Phase APB)
                    PENABLE     <= 1'b1;
                    HREADY_OUT  <= 1'b1;
                end

                default: begin
                    HRDATA      <= 0;
                    HRESP       <= 0;
                    HREADY_OUT  <= 0;
                    PSEL        <= 0;
                    PENABLE     <= 0;
                    PADDR       <= 0;
                    PWRITE      <= 0;
                    PWDATA      <= 0;
                end
            endcase
        end
    end


    // Valid Signal Combinational Logic
    always_comb begin : VALID
        // Transaction is valid only if slave (bridge) is selected
        // & HTRANS is either NONSEQ or SEQ
        valid = HSEL && HTRANS[1];
    end


endmodule