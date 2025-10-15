# 🧩 AMBA Protocols

This repository contains **SystemVerilog implementations and verification** of **AMBA (Advanced Microcontroller Bus Architecture)** protocols, currently an **AHB-to-APB bridge**.  
The goal is to understand and model **bus-level communication protocols** widely used in SoCs for connecting high-performance and peripheral devices.

---

## 📑 Table of Contents

* [Introduction](#-introduction)
* [AMBA Overview](#-amba-overview)
* [Need for AHB-to-APB Bridge](#-need-for-ahb-to-apb-bridge)
* [Bridge Architecture](#-bridge-architecture)
* [Repository Structure](#-repository-structure)
* [Future Work](#-future-work)
* [References](#-references)
* [License](#-license)
* [Contributions](#-contributions)

---

## 📊 Introduction

The **Advanced Microcontroller Bus Architecture (AMBA)** family of protocols by ARM defines **standardized interfaces** for communication between components in a System-on-Chip (SoC).  
It improves interoperability between IP cores and simplifies integration by providing well-defined **bus interfaces** for masters, slaves, and bridges.

This repository includes:

- ✅ **Synchronous AHB-to-APB bridge** implementation with FSM-based control  
- ✅ **Testbenches** to validate protocol behavior  
- ✅ Parameterized and reusable SystemVerilog code
- ✅ AHB APB Interfaces for easy future extension

---

## 🧠 AMBA Overview

The AMBA specification defines multiple bus protocols tailored to different performance and complexity requirements:

| Protocol | Purpose | Typical Use Case |
|-----------|----------|------------------|
| **AHB (Advanced High-performance Bus)** | High-performance, pipelined system bus | CPU, DMA, Memory, High-speed peripherals |
| **APB (Advanced Peripheral Bus)**  | Low-power, simple interface | UART, Timer, GPIO, Low-speed peripherals |
| **AXI (Advanced eXtensible Interface)** | High-performance, high-frequency bus with burst and out-of-order transactions | Multi-core CPUs, GPUs, DDR controllers |

Each protocol builds upon the previous one, allowing a **hierarchical interconnect**.  
The AHB and AXI buses are typically used in **high-speed domains**, while APB is used for **low-speed peripheral access**.

![AMBA System](imgs/amba_system.png)

---

## 🔄 Need for AHB-to-APB Bridge

The **AHB-to-APB bridge** acts as a protocol converter between the **high-performance AHB system bus** and the **low-power APB peripheral bus**.  
Since AHB supports pipelined, burst-based communication and APB is non-pipelined, a bridge is required to **translate transactions** while maintaining timing and data integrity.

**Key responsibilities of the AHB-to-APB bridge:**
1. Decode AHB address and generate corresponding **PSEL** for the targeted APB slave.
2. Manage **handshaking and timing** between clock domains (if `HCLK` ≠ `PCLK`).
3. Convert AHB **read/write control signals** into APB-compliant signals.
4. Insert appropriate **wait states** to synchronize slower peripherals.

---

## 🧱 Bridge Architecture

The AHB-to-APB bridge consists of:
- **Address Decoder** — Identifies which APB slave is being accessed. (Single slave in this repo so no decoding)
- **Clock Domain crossing handshake** — Use FIFO or handshaking with synchrnoizers in case asynchrnouns bridge. (This repo has implementation of a synchrnous bridge)
- **State Machine (FSM)** — Controls signal transitions across the two protocols.
- **Register Stage** — Buffers data and address signals between AHB and APB domains.
- 
![AHB2APB Bridge Block Diagram](imgs/ahb2apb_bridge_block_diagram.png)

*(FSM diagram source: ARM Example AMBA System Technical Reference Manual [DDI0170])*  

### 🔌 Block Diagram

The following diagram shows the **connectivity and signal flow** between the AHB and APB domains through the bridge:

![AHB2APB Bridge Inputs/Outputs](imgs/ahb2apb_bridge_output.png)

---

### ⚙️ FSM Description

The **Finite State Machine (FSM)** manages protocol conversion between AHB and APB phases.  
It ensures correct signal sequencing for setup and enable phases of the APB, while responding appropriately to AHB transactions.

![AHB2APB Bridge State Machine](imgs/ahb2apb_bridge_fsm.png)

*(FSM diagram source: ARM Example AMBA System Technical Reference Manual [DDI0170])*  

**FSM States:**
1. **ST_IDLE** – Idle state where PSEL and PENABLE are low, waiting for a valid AHB read or write transfer.
2. **ST_READ** – Sets up an APB read transfer and asserting the appropriate PSEL.
3. **ST_WWAIT** – Waits for AHB write data to become valid before starting the corresponding APB write transfer.
4. **ST_WRITE** – Initiates an APB write by asserting PSEL and PWRITE, completing a single write transfer.
5. **ST_WRITEP** – Handles a pipelined APB write while inserting a wait state to maintain AHB-APB synchronization.
6. **ST_RENABLE** – Enables the APB read transfer by asserting PENABLE for data phase completion.
7. **ST_WENABLE** – Enables the APB write transfer by asserting PENABLE for data phase completion.
8. **ST_WENABLEP** – Manages pending transfers, inserting a wait state when a read follows a write to ensure proper sequencing.

---

## 📂 Repository Structure

```

src/
├── ahb_interface.sv          # AHB interface definition
├── ahb_to_apb_bridge.sv      # Bridge module with FSM
├── apb_interface.sv          # APB interface definition
└── apb_mem.sv                # Simple APB memory slave
tb/
├── ahb_to_apb_bridge_tb.sv   # Testbench for bridge verification
imgs/
LICENSE
README.md

```

---

## 🧭 Future Work

* 🧩 Implement AHB Arbiter and Decoder for multi-master systems  
* 🔄 Add AXI-based interconnect and bridge examples  
* ⚙️ Integrate multi-master and multi-slave support  
* 🧪 Develop **UVM-based verification** environment for coverage and assertions  

---

## 🔗 References

1. **ARM Ltd.**, *AMBA 3 AHB-Lite and APB Protocol Specification*  
   [https://developer.arm.com/documentation/ddi0170/a/AHB-Modules](https://developer.arm.com/documentation/ddi0170/a/AHB-Modules)
2. **ARM IHI0024C**, *AMBA 3 APB Protocol Specification*  
3. **ARM IHI0033A**, *AMBA 3 AHB-Lite Protocol Specification*  

---

## 📄 License

This project is released under the **MIT License**.  
See the [LICENSE](LICENSE) file for details.

---

## 🤝 Contributions

Contributions, bug reports, and feature suggestions are welcome!  
Feel free to fork the repository and submit a pull request.

---

*Created by **Talha Israr***  
```

---