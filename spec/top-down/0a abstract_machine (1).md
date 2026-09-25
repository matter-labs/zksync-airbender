## Machine

Airbender provides execution consistency proofs for abstract RISC-V 32IM ISA like little-endian CPU with few custom extensions. We use a notion of "timestamp" to both indicate a logical sequence of CPU cycles, and as implementation detail where needed.

### Machine state

Machine state can be viewed interchangable as both:
- union of:
    - PC and timestamp
    - RAM - up to (4GB - 4Mb) addressable space from 4Mb address mark
    - ROM - lowest 4Mb of addressable space from 0 address mark
    - RAM and ROM form uniform addressable space
    - 32 standard RISC-V 32-bit registers
- read and write sets of tuples (address space: valid values below, address: 32 bit value represented as 16 bit limbs x 2, value: 32 bit value represented as 16 bit limbs x 2, timestamp: 38 bit value represented as 19 bit limbs x 2) for 3 various types of address spaces:
    - address space 0 is RAM. Address is RAM offset
    - address space 1 is registers. Address is register index
    - address space 2 for PC. Address is always 0

The reduction showing how an N-cycle execution of the given program, starting from the initial conditions below, is proven consistent through a permutation argument over its read and write sets will be given separately.

### Provable execution sequences

Machine can prove an execution of N sequential cycles from initial conditions (below) for any RISC-V program that:
- does not encounter unsupported opcodes during N executed cycles. NOTE: program CAN contain unsupported opcodes in it's binary, but if branches with such opcodes are never taken during execution then such cycle sequence is provable
- does not provoke exceptions by RISC-V spec in runtime (e.g. unaligned jump destinations)
- does not attempt to perform writes to ROM address range
- does not perform unaligned memory accesses
- fits within 2^36 - 1 cycles bound

NOTES:
- whether the program being proven has reached it's logical termination or not during those N cycles is responsibility of the verifier based on final registers values and PC
- verifier (assuming it has an access to program's bytecode) can also check that at the cycle N+1 execution will encounter an exception if needed: RISC-V runtime exceptions can be resolved purely from register's values and opcode. RAM content witness is not required

### Initial conditions

Can be viewed as both:
- abstract CPU:
    - PC = 0
    - all registers are zeros
    - RAM is all zeros
    - ROM filled with flattened executed binary (flattening is implementation detail related to ELF file format and linker scripts)
- read and write sets
    - read set is empty
    - write set contains:
        - (address space 2, address 0, value PC = 0, timestamp 4)
        - for all registers x0..=x31: entries (address space 1, address = register index, value = 0, timestamp 0)
        - NOTE: address space for registers is much larger and >=32 register indexes may occur in read and write sets during program execution, but there are no entries for them in the initial write set
        - for RAM address space continuous subranges (implementation detail) where all touched RAM cells are located: entried like (address space 0, address = RAM offset, always 0 mode 4, value = 0, timestamp 0)
        - NOTE: RAM address space cells that were never read or written by the executed program are unobservable and usually ignored by memory consitency arguments. Usage of continous subranges above is implementation detail


### Sharded and predicated execution

Small level of implementation detail is inevitable in this section. System contains from 3 fundamental circuit's logical types, and in some configuration modes types can be merged into particular single instance via batch commitment and GKR arguments

- Circuit type "family circuit" - logically responsible for processing of RISC-V instructions. Circuit's setup for such type is program-dependent, and execution is predicated
- Circuit type "precompile" - logically responsible to applying results of complex execution directly to RAM (and only RAM). Circuit's setup for such type is NOT program-dependent, and execution is predicated
- Circuit type "inits and teardowns" - particular choice of memory consistency argument chosen for implementation requires prover to provide final value of all cells in all address spaces (see read and write sets above). Providing such set for RAM space is too expensive for the verifier in plain text, so it is provided as witness. Circuit's setup for such type is NOT program-dependent, and execution is NOT predicated

Each circuit being proven as a part of machine execution belongs to one of the families and is of fixed capacity (due to choices of arithmetization and polynomial commitment schemes) that is called "cycle" or "row" (if one imagines arithmetization as a table like AIR arithmetization). For that reason predicated execution is needed that can be viewed both as:
- logically: if predicate is "false" for particular cycle then machine state is unchanged
- implementation: if predicate is "false" for particular cycle then content of read and write sets is unchanged

### Final values available for the verifier to observe:

TODO!