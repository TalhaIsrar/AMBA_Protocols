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

    // Ensure PADDR is stable if PSEL and PENABLE = 1
    property stable_paddr;
        @(posedge HCLK) disable iff (!HRESETn)
        (PSEL && PENABLE) |-> $stable(PADDR);
    endproperty

    assert property (stable_paddr)
        else $error("SVA: PADDR is not stable when PENABLE & PSEL = 1");

    // HWRITE followed by PWRITE at proper time at some point in future when PENABLE = 1
    property p_ahb_write_to_apb_write;
        @(posedge HCLK) disable iff (!HRESETn)
        ($fell(HSEL) && HTRANS[1] && HWRITE) |=> ##[1:$] PENABLE |-> PWRITE;
    endproperty
    assert property (p_ahb_write_to_apb_write)
        else $error("SVA: APB PENABLE went high but PWRITE went low when HWRITE was high");

    // HWRITE followed by PWRITE at proper time at some point in future when PENABLE = 1
    property p_ahb_write_to_apb_write_opposite;
        @(posedge HCLK) disable iff (!HRESETn)
        ($fell(HSEL) && HTRANS[1] && !HWRITE) |=> ##[1:$] PENABLE |-> !PWRITE;
    endproperty
    assert property (p_ahb_write_to_apb_write_opposite)
        else $error("SVA: APB PENABLE went high but PWRITE went high when HWRITE was low");

    // Ensure valid transfer
    property p_ahb_valid_transfer;
        @(posedge HCLK) disable iff (!HRESETn)
        HSEL |-> HTRANS[1];
    endproperty
    assert property (p_ahb_valid_transfer)
        else $warning("SVA: PTRANS[1] is not 1 when HSEL is asserted");

    // PENABLE must drop after 1 cycle
    property p_apb_enable_off;
        @(posedge HCLK) disable iff (!HRESETn)
        PENABLE |-> ##1 !PENABLE;
    endproperty
    assert property (p_apb_enable_off)
        else $error("SVA: PENABLE stayed high for more than one cycle!");

    // PSEL is followed in future after HSEL
    property p_sel_after_h_sel;
        @(posedge HCLK) disable iff (!HRESETn)
        ($fell(HSEL) && HTRANS[1] && HWRITE) |=> ##[1:$] PSEL;
    endproperty
    assert property (p_sel_after_h_sel)
        else $error("SVA: PSEL did not go high after HSEL came");

    // PADDR is correctly changed after HSEL comes
    logic [31:0] haddr_latched;

    always @(posedge HCLK or negedge HRESETn) begin
        if (!HRESETn)
            haddr_latched <= 32'h0;
        else if ($fell(HSEL) && HTRANS[1])
            haddr_latched <= HADDR;
    end

    property p_write_addr_follow;
        @(posedge HCLK) disable iff (!HRESETn)
        ($fell(HSEL) && HTRANS[1])
            |=> ##[1:$] ($changed(PADDR) && (PADDR == haddr_latched));
    endproperty

    assert property (p_write_addr_follow)
        else $fatal("SVA: When HWRITE occurred, PADDR did not match HADDR when it changed");


endmodule
