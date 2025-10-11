module apb_mem #(
  parameter ADDR_WIDTH = 8,       // 256 bytes
  parameter DATA_WIDTH = 32
)(
  input  logic                  PCLK,
  input  logic                  PRESETn,
  input  logic [ADDR_WIDTH-1:0] PADDR,
  input  logic [DATA_WIDTH-1:0] PWDATA,
  input  logic                  PWRITE,
  input  logic                  PSEL,
  input  logic                  PENABLE,
  output logic [DATA_WIDTH-1:0] PRDATA
);

  // Memory array
  logic [DATA_WIDTH-1:0] mem [0:(1<<ADDR_WIDTH)/4 - 1];

  // Read/Write operation
  always_ff @(posedge PCLK or negedge PRESETn) begin
    if (!PRESETn) begin
      PRDATA <= '0;
    end else if (PSEL && PENABLE) begin
      if (PWRITE)
        mem[PADDR[ADDR_WIDTH-1:2]] <= PWDATA;   // word-aligned write
      else
        PRDATA <= mem[PADDR[ADDR_WIDTH-1:2]];   // word-aligned read
    end
  end

endmodule
