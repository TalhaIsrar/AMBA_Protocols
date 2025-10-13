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
    logic valid;                            // AHB transfer valid
    logic APBen;                            // Enable signal for new APB transcation

    logic HwriteReg;                        // Buffered HWRITE
    logic HselReg;                          // Buffered HSEL
    logic [ADDR_WIDTH - 1:0] PAddrReg;      // Buffered address HADDR
    logic [ADDR_WIDTH - 1:0] AddressReg;    // Buffered address PADDR
    logic [DATA_WIDTH - 1:0] DataReg;       // Buffered Data
    logic HReadyReg;                        // Buffered HREADY_OUT Signal
    logic PenReg;                           // Buffered PEnable
    logic PWriteReg;                        // Buffered PWrite

    logic PenNext;                          // PEnable next
    logic PSelNext;                         // PSEL based on state  
    logic PWriteNext;                       // PWrite next
    logic HReadyNext;                       // HREADY_OUT next


    // State variable for state machine
    typedef enum logic [2:0] {
        ST_IDLE     = 3'b000,
        ST_READ     = 3'b001,
        ST_RENABLE  = 3'b010,
        ST_WENABLE  = 3'b011,
        ST_WRITE    = 3'b100,
        ST_WWAIT    = 3'b101,
        ST_WRITEP   = 3'b110,
        ST_WENABLEP = 3'b111
    } bridge_states;

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

            default: next_state = ST_IDLE;
        endcase
    end

    // Generate APBen Signal & Next output signals
    always_comb begin
        APBen = next_state == ST_READ || next_state == ST_WRITE || next_state == ST_WRITEP;
        PenNext = next_state == ST_RENABLE || next_state == ST_WENABLE || next_state == ST_WENABLEP;
        PSelNext = next_state == ST_READ || next_state == ST_RENABLE || next_state == ST_WRITE ||
                   next_state == ST_WENABLE || next_state == ST_WENABLEP || next_state == ST_WRITEP;
        PWriteNext = next_state == ST_WRITE || next_state == ST_WRITEP;
        HReadyNext = !(next_state == ST_READ || next_state == ST_WRITEP || (next_state == ST_WENABLEP && !HWRITE));
    end

    // Buffer signals
    always_ff @(posedge HCLK or negedge HRESETn) begin
        if (!HRESETn) begin
            HwriteReg  <= 0;
            HselReg    <= 0;
            AddressReg <= 0;
            HReadyReg  <= 1'b1;
            PWriteReg  <= 0;
            DataReg    <= 0;
            PenReg     <= 0;
        end else begin
            PAddrReg <= HADDR;

            if (APBen) begin
                PWriteReg  <= PWriteNext;
                HselReg    <= PSelNext;
                AddressReg <= HWRITE ? PAddrReg : HADDR;
            end

            HwriteReg  <= HWRITE;
            DataReg <= HWDATA;
            PenReg  <= PenNext;
            HReadyReg  <= HReadyNext;
        end
    end

    // Output logic
    always_comb begin : OUTPUT_LOGIC
        // Default values to avoid latches
        PWDATA      = DataReg;        
        PENABLE     = PenReg;
        PSEL        = HselReg;
        PADDR       = AddressReg;
        PWRITE      = PWriteReg;

        HRESP       = 2'b00;       // Always OKAY
        HRDATA      = PRDATA;
        HREADY_OUT  = HReadyReg;
    end

    // Valid Signal Combinational Logic
    always_comb begin : VALID
        // Transaction is valid only if slave (bridge) is selected
        // & HTRANS is either NONSEQ or SEQ
        valid = HSEL && HTRANS[1] && HREADY_OUT;
    end

endmodule