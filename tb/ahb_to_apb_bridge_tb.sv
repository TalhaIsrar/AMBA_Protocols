'timescale 1ns/1ps

module ahb_to_apb_bridge_tb;

    parameter ADDR_WIDTH = 32;
    parameter DATA_WIDTH = 32;

    // Clock and reset
    logic HCLK, HRESETn;
    logic PCLK, PRESETn;    

    // Interfaces
    ahb_interface #(ADDR_WIDTH, DATA_WIDTH) ahb_bus(.HCLK(HCLK), .HRESETn(HRESETn));
    apb_interface #(ADDR_WIDTH, DATA_WIDTH) apb_bus(.PCLK(PCLK), .PRESETn(PRESETn));

    // DUT
    ahb_to_apb_bridge #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) dut (
        // AHB Slave side
        .HCLK       (HCLK),
        .HRESETn    (HRESETn),
        .HSEL       (ahb_bus.HSEL),
        .HADDR      (ahb_bus.HADDR),
        .HTRANS     (ahb_bus.HTRANS),
        .HWRITE     (ahb_bus.HWRITE),
        .HREADY_IN  (ahb_bus.HREADY_IN),
        .HWDATA     (ahb_bus.HWDATA),
        .HRDATA     (ahb_bus.HRDATA),
        .HRESP      (ahb_bus.HRESP),
        .HREADY_OUT (ahb_bus.HREADY_OUT),

        // APB Master side
        .PRDATA     (apb_bus.PRDATA),
        .PSEL       (apb_bus.PSEL),
        .PENABLE    (apb_bus.PENABLE),
        .PADDR      (apb_bus.PADDR),
        .PWRITE     (apb_bus.PWRITE),
        .PWDATA     (apb_bus.PWDATA)
    );

    // Clock generation
    initial begin
        HCLK = 0;
        forever #5 HCLK = ~HCLK; // 100 MHz
    end

    assign PCLK = HCLK; // For now, same clock domain
    assign PRESETn = HRESETn;

    // Reset generation
    initial begin
        HRESETn = 0;
        #20;
        HRESETn = 1;
    end

    // Simple AHB Master Tasks
    task ahb_master_write(input logic [31:0] addr, input logic [31:0] data);
        @(posedge HCLK);
        ahb_bus.HSEL      <= 1'b1;
        ahb_bus.HTRANS    <= 2'b10;
        ahb_bus.HWRITE    <= 1'b1;
        ahb_bus.HADDR     <= addr;
        ahb_bus.HWDATA    <= data;
        ahb_bus.HREADY_IN <= 1'b1;
        @(posedge HCLK);
        ahb_bus.HTRANS    <= 2'b00;
        ahb_bus.HSEL      <= 1'b0;
    endtask

    task ahb_master_read(input logic [31:0] addr);
        @(posedge HCLK);
        ahb_bus.HSEL      <= 1'b1;
        ahb_bus.HTRANS    <= 2'b10;
        ahb_bus.HWRITE    <= 1'b0;
        ahb_bus.HADDR     <= addr;
        ahb_bus.HREADY_IN <= 1'b1;
        @(posedge HCLK);
        ahb_bus.HTRANS    <= 2'b00;
        ahb_bus.HSEL      <= 1'b0;
    endtask

    // Stimulus
    initial begin
        @(posedge HRESETn);
        repeat (2) @(posedge HCLK);
        ahb_master_write(32'h0000_0004, 32'hDEAD_BEEF);
        repeat (2) @(posedge HCLK);
        ahb_master_read(32'h0000_0004);
        repeat (5) @(posedge HCLK);
        $finish;
    end

endmodule