# Philosophy and Logic

## System Architecture

Our RISC-V 32I+M proving machine consists of highly optimized DEEP STARK/FRI arguments, Lookup/RAM/Delegation arguments, AIR constraints for the RISC-V CPU and precompiles (BLAKE2s/Blake3 and U256 BigInt operations), along with a custom Rust verifier program for recursion, and a CPU OS "kernel" program for user-facing EVM emulation —not present in this repository. 

Custom "machine configuration" variants of the CPU circuit are provided to disable features at will (e.g., signed multiplication) or to enable new instructions (e.g., basic modular field element operations) during recursion. Some system-level opcodes that do not fit our proving context are disallowed (e.g., `ECALL`/`WFI`/`FENCE`/`CSR`), as are all inefficient unaligned full-word memory accesses and odd half-word accesses. Trap handling is not processed via internal CPU state; instead, traps are immediately caught and converted to unprovable constraints, ensuring that our "kernel" OS crashes the prover whenever a bug is found. 

CPU calls to custom "precompile" circuits and accesses to *non-deterministic* long-term memory storage are performed exclusively through the `CSRRW` opcode, which is then converted to Delegation argument calls. Further necessary call information is passed through RAM via a custom ABI. The RISC-V constraints follow a common fetch-decode-execute loop, performed exclusively in the highest privilege machine mode, which is identically enforced at each cycle and row of our witness trace. 

All arithmetization is performed over Mersenne31 field elements, except when security requires switching to the extension field (e.g., Lookup finalization). Since our CPU simulates 32-bit words, we have split most of them into 16-bit limbs. All 32-bit registers are kept in a separate address space, relegating register access to the RAM argument and keeping only a minimal shared state of field element variables across cycles (e.g., Program Counter). RISC-V bytecode to be executed is kept in a so-called "ROM" which is physically accessed through a preprocessed Lookup table and virtually inhabits a reserved address space portion of the RAM, which is itself devoid of any further paging or translation layers. 

The maximum total RISC-V CPU cycles executed in a single run of the proving machine are in the order of $2^{36} - 2^{14}$, chunked into batches of around $2^{22}$ cycles. These batches are then individually proven for a specific circuit and connected by "global" RAM and Delegation arguments. Finally, chunks are joined via multiple recursion phases until the final proof is obtained. 

All AIR constraints are kept at a maximum of degree 2 polynomials, which streamlines proving optimizations for STARK/FRI and distills circuit performance analysis to the counting of total field element variables used at each cycle; for example, the number of witness trace columns present in each row. 

Preliminary minimal witness generation is natively performed by a fast Rust RISC-V simulator on a CPU, and quickly handed over to a CUDA-compatible GPU, where much faster circuit-specific witness generation and proving can be completed. This repo contains both CPU and GPU prover implementations that mirror each other. 

Stages for each proving chunk follow a linear structure: 
- Stage 1: Computes witness LDEs and Trace Commitments.
- Stage 2: Sets up Lookup and Memory arguments. 
- Stage 3: Computes the primary STARK Quotient Polynomial.
- Stage 4: Computes the DEEP optimization (FRI Batched) Polynomial.
- Stage 5: Computes the required IOPP (FRI) proof.

## Details

Even though our purpose is to prove RISC-V bytecode execution per se, we should understand that we effectively start mixing more and more code expressed in standard programming language, compiler assumptions, and circuits. 

One notable example is the existence of a special "non-determinism" register abstraction, which is available for high-level programming language access. This allows for cheaper proofs of execution **without** (!) special circuits in some special cases, like hash-to-prime routines, where it's possible to compute some witnesses outside, as often done in usual circuits. Then, it provides them to the user's program and verifies by spending fewer cycles than brute-force computation in the provable environment.

We have three programming models that we want to support, each relying on different degrees of strictness and control over compiler output:

1. **Standard kernel-mode program**: Without special assumptions about the code and compiler features, like the usage of the RV32I+M instruction sets. This will be used to run ZKsync OS itself. In this case, we can generally assume correctness/good behavior of the compiler, so we do not want to handle/trap cases like unaligned memory access. A standard compiler would not try to issue, e.g., attempts to read `u32` at an address that is not `0 mod 4` unless instructed otherwise. Note that none of the kernel-only (machine privilege only) configurations will support `ECALL/EBREAK/WFI` instructions for two reasons: first one, efficiency, as such instructions touch too many aspects of the internal machine state; and second logic, as in kernel you don't need an `ECALL` to call any function that is reachable by pointer in a system without MMU.

2. **Reduced instruction set**: For programs that we want to prove in practice, there is no need to support signed multiplication/division opcodes that take a large part of the circuits. This is a configuration like the one above, but without support for `DIV`/`REM`/`MULH`/`MULHSU` opcodes.

3. **Recursion-only mode**: Where we have very good control over the compiler output of one single specific program. This way, we can avoid supporting divisions/multiplications, less-than-word memory accesses, and provide handy ops like special opcodes (from `MOP` address space) for field arithmetic. This leads to both a smaller circuit and fewer cycles to prove.

## Limitations over programs

While the following limitations apply to all programs executed on top of our RISC-V CPU, it is worth noting that in practice, ZKsync user-provided programs will not run directly on the "bare-metal" CPU. Instead, they will be processed by the ZKsync OS kernel program and any VM interpreter contained therein, including the EVM interpreter. 

It is, then, the primary responsibility of the trusted EVM/VM interpreter —in combination with ZKsync OS— to guarantee memory and resource safety by offering a layer of protection between the CPU and potentially unsafe user-provided programs, as well as between each other. Resource control is also part of this intermediate layer, for example, for preventing costly infinite loop attacks.

As such, ZKsync users are unlikely to be especially affected by or concerned with the following limitations, which are primarily of interest to the technical reader.

- **No support for bytecode in generic RAM**: We assume that bytecode is placed in a memory sub-range that is modeled as ROM.
- **No support for runtime-loaded bytecode**
- **No loader**: Bytecode is dumped via `objdump`, and the resulting flat binary is placed in the ROM. There is no support for mutable non-trivially (non-zero) initialized variables. The ELF `.data` section is expected to be empty. Programs that do not use `static` variables are completely fine with this. If such a variable is needed, it can be implemented via `MaybeUninit` in Rust terms, with manual initialization. We may spend some time to check what can be done better about this.
- **End of execution behavior**: The end of execution is checked by the verifier, and requires particular behavior of the program; it must just loop at the end. This implementation is provided via the corresponding crate.
- **Success assumption**: In general, we assume that the intention of running the program is to show that it ended "successfully", so it didn't panic at the end of the day, as that would be an unprovable circuit. Whether the logical result of this program is "success" or "error" is not for us to interpret.

## Design shortcomings

Currently, the version of the system presented in the `main` branch is over-generalized. For example, every cycle contains decoder logic, where the opcode (as `u32`) is parsed to understand what instruction we execute this cycle (or trap == unprovable circuit) otherwise. 

We do not currently support bytecode located in the RAM region of memory, or any other form of dynamic bytecode loading for execution. This would be required if untrusted native RISC-V bytecode were supported, which in turn would also require *U-mode* support. Instead, we model the text section in ROM as a lookup between PC and the fully decoded bytecode information in circuits. There are some other places with similar inefficiencies.

In one of the branches, there is another approach for state transition design, largely inspired by our RAM argument. We can model every cycle as a state transition that maps internal machine state (in our case, it's just PC and timestamp) into another state (potentially touching memory along the way), with the initial state (initial write set) being `(0, INITIAL_TS)`. 

At the end of the cycle, we add `(final PC, final timestamp)` to the write set, and `(initial PC, initial timestamp)` to the read set. Then we define a set of opcode-family specialized circuits, where `PC` is always looked up from the special table (generated from the bytecode), where only `PC` values with particular opcodes are present. 

This way, we can have almost 100% efficient (every circuit variable participates in every opcode - it's a dream for all VM designs) circuits for addition/subtraction, another one for multiplication/division, and so on. Optimizations from such an approach can be backported into the current approach (e.g., decoder table) almost in full, as the current formulation of the VM is needed for recursion purposes. At some point it's more efficient to go from a few different kinds(!) of circuits, each being more efficient to fewer different kinds for fewer concrete number(!) of circuits to verify in recursion step.
