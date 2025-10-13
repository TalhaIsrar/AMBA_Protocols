`timescale 1ns/1ps

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

    apb_mem slave (
        .PCLK     (PCLK),
        .PRESETn  (PRESETn),
        .PADDR    (apb_bus.PADDR),
        .PWDATA   (apb_bus.PWDATA),
        .PWRITE   (apb_bus.PWRITE),
        .PSEL     (apb_bus.PSEL),
        .PENABLE  (apb_bus.PENABLE),
        .PRDATA   (apb_bus.PRDATA)
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

    // Reset initial input signals
    initial begin
        ahb_bus.HSEL      <= 1'b0;
        ahb_bus.HTRANS    <= 2'b00;  
        ahb_bus.HWRITE    <= 1'b0;
        ahb_bus.HADDR     <= '0;
        ahb_bus.HREADY_IN <= 1'b0;
        ahb_bus.HWDATA    <= '0;

        apb_bus.PRDATA    <= '0;
    end

    // Simple AHB Master Tasks
    // AHB Write: address phase then data phase
    task ahb_master_write(input logic [31:0] addr, input logic [31:0] data);
        // Address phase
        @(negedge HCLK);
        ahb_bus.HSEL      <= 1'b1;
        ahb_bus.HTRANS    <= 2'b10;   // NONSEQ
        ahb_bus.HWRITE    <= 1'b1;
        ahb_bus.HADDR     <= addr;
        ahb_bus.HREADY_IN <= 1'b1;

        // Data phase (next cycle)
        @(negedge HCLK);
        ahb_bus.HWDATA    <= data;
        
        // Return to IDLE
        ahb_bus.HTRANS    <= 2'b00;
        ahb_bus.HSEL      <= 1'b0;
        ahb_bus.HADDR     <= 32'h0000_0000;

        @(negedge HCLK);
    endtask

    // AHB Read: address phase, then capture HRDATA after data phase
    task ahb_master_read(input logic [31:0] addr);
        // Address phase
        @(negedge HCLK);
        ahb_bus.HSEL      <= 1'b1;
        ahb_bus.HTRANS    <= 2'b10;   // NONSEQ
        ahb_bus.HWRITE    <= 1'b0;
        ahb_bus.HADDR     <= addr;
        ahb_bus.HREADY_IN <= 1'b1;

        // Return to IDLE
        @(negedge HCLK);
        ahb_bus.HTRANS    <= 2'b00;
        ahb_bus.HSEL      <= 1'b0;

        @(negedge HCLK);
    endtask

    // AHB Pipelined Write
    task ahb_master_pipelined_write(input logic [31:0] addr1, addr2,
                                    input logic [31:0] data1, data2);
        // First transfer - address phase
        @(negedge HCLK);
        ahb_bus.HSEL      <= 1'b1;
        ahb_bus.HTRANS    <= 2'b10;   // NONSEQ
        ahb_bus.HWRITE    <= 1'b1;
        ahb_bus.HADDR     <= addr1;
        ahb_bus.HREADY_IN <= 1'b1;

        // Wait for bridge ready before proceeding to data phase
        @(posedge HCLK);
        #1
        wait (ahb_bus.HREADY_OUT == 1'b1);

        // Data phase of first, address phase of second
        @(negedge HCLK);
        ahb_bus.HWDATA <= data1;
        ahb_bus.HADDR  <= addr2;

        // Again, wait for bridge ready before data phase 2
        @(posedge HCLK);
        #1
        wait (ahb_bus.HREADY_OUT == 1'b1);

        // Data phase 2
        @(negedge HCLK);

        ahb_bus.HWDATA <= data2;
        ahb_bus.HTRANS <= 2'b00;
        ahb_bus.HSEL   <= 1'b0;
        ahb_bus.HADDR  <= 32'h0;

        @(posedge HCLK);
        #1
        wait (ahb_bus.HREADY_OUT == 1'b1);

        @(negedge HCLK);
    endtask

    // AHB Pipelined Read
    task ahb_master_pipelined_read(input logic [31:0] addr1, addr2);
        // Address phase
        @(negedge HCLK);
        ahb_bus.HSEL      <= 1'b1;
        ahb_bus.HTRANS    <= 2'b10;   // NONSEQ
        ahb_bus.HWRITE    <= 1'b0;
        ahb_bus.HADDR     <= addr1;
        ahb_bus.HREADY_IN <= 1'b1;

        // Wait for bridge ready before proceeding to data phase
        @(posedge HCLK);
        #1
        wait (ahb_bus.HREADY_OUT == 1'b1);

        // Data phase of first, address phase of second
        @(negedge HCLK);
        ahb_bus.HADDR  <= addr2;

        // Again, wait for bridge ready before data phase 2
        @(posedge HCLK);
        #1
        wait (ahb_bus.HREADY_OUT == 1'b1);
    
        // Data phase 2
        @(negedge HCLK);

        ahb_bus.HTRANS <= 2'b00;
        ahb_bus.HSEL   <= 1'b0;
        ahb_bus.HADDR  <= 32'h0;

        @(posedge HCLK);
        #1
        wait (ahb_bus.HREADY_OUT == 1'b1);

        @(negedge HCLK);  

    endtask

    // Stimulus
    initial begin
        @(posedge HRESETn);

        // Test 1: Single Transfers
        repeat (2) @(posedge HCLK);

        ahb_master_write(32'h0000_0004, 32'hBEEF_BEEF);
        ahb_master_read(32'h0000_0004);

        // Test 2: Two back-to-back writes
        ahb_master_write(32'h0000_0004, 32'hDEAD_BEEF);
        ahb_master_write(32'h0000_0008, 32'hBEEF_CAFE);

        // Test 3: Back-to-back read after write
        ahb_master_write(32'h0000_000C, 32'hFACE_FEED);
        ahb_master_read(32'h0000_000C); 

        // Test 4: Sequential address writes
        for (int i = 0; i < 4; i++) begin
            ahb_master_write(32'h0000_0020 + i*4, 32'h1000_0000 + i);
        end

        // Sequential reads
        for (int i = 0; i < 4; i++) begin
            ahb_master_read(32'h0000_0020 + i*4);
        end

        // Test 5: Randomized test
        repeat (5) begin
            logic [31:0] addr = {$random} & 32'h0000_00FF;
            logic [31:0] data = $random;
            ahb_master_write(addr, data);
            ahb_master_read(addr);
        end

        // Test 6: Alternating operations
        ahb_master_write(32'h0000_0030, 32'hAAAA_0001);
        ahb_master_read(32'h0000_0030);
        ahb_master_write(32'h0000_0034, 32'hBBBB_0002);
        ahb_master_read(32'h0000_0034);

        // Test 7: No valid transfer when HSEL=0
        @(negedge HCLK);
        ahb_bus.HSEL   <= 1'b0;
        ahb_bus.HTRANS <= 2'b00;
        ahb_bus.HWRITE <= 1'b1;
        ahb_bus.HADDR  <= 32'h0000_0040;
        ahb_bus.HWDATA <= 32'h5555_5555;
        repeat (2) @(posedge HCLK);
        assert(apb_bus.PENABLE === 1'b0)
            else $error("Bridge triggered APB transaction when PENABLE=0");
 
        // Test 8: Idle period test
        ahb_master_write(32'h0000_0050, 32'hCAFEBEEF);
        repeat(10) @(posedge HCLK);  // idle gap
        ahb_master_read(32'h0000_0050);
        
        // Test 9 : Pipelined Write
        ahb_master_pipelined_write(32'h0000_0010, 32'h0000_0014,
                                   32'h0000_1234, 32'h0000_4321);

        // Test 10: Pipelined Read
        ahb_master_pipelined_read(32'h0000_0010, 32'h0000_0014);

        repeat(5) @(posedge HCLK);
        $display("All tests executed!");
        $finish;
    end

endmodule