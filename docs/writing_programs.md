### Writing Programs for the RISC-V AirBender

This tutorial shows how to write, build, and run RISC‑V programs for AirBender. It explains the minimal runtime setup your binary needs, how to produce outputs the simulator/prover understands, and how to call delegations (precompiles) from your program.

## Program skeleton (no_std, no_main, entry, traps)

AirBender executes bare‑metal RISC‑V code. Since there's no OS, you have to provide a little bootstrap so your program can start and return its result. A minimal skeleton looks like this:

```rust
// On bare metal, std isn’t available. You need to use core instead, and you provide your own startup, panic, I/O, etc. Some embedded patterns (custom allocators, generic const exprs) need nightly. In this file you don’t actually use allocator_api or generic_const_exprs.
#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
//We are telling Rust not to generate the usual main/crt startup. We are providing our own entrypoint (assembly and a custom _start_rust symbol).
#![no_main]

use riscv_common::zksync_os_finish_success;

extern "C" {
    // Boundaries of the heap
    static mut _sheap: usize;
    static mut _eheap: usize;

    // Boundaries of the stack
    static mut _sstack: usize;
    static mut _estack: usize;

    // Boundaries of the data region - to init .data section. Yet unused
    static mut _sdata: usize;
    static mut _edata: usize;
    static mut _sidata: usize;
}

// Bring in the minimal boot/ABI glue.
core::arch::global_asm!(include_str!("../../scripts/asm/asm_reduced.S"));

// Minimal stub to satisfy the compiler for exception handling metadata in a no_std binary.
#[no_mangle]
extern "C" fn eh_personality() {}

// The entry point that the assembler boot code jumps into.
#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}
// Declares an external trap entry.
#[export_name = "_setup_interrupts"]
pub unsafe fn custom_setup_interrupts() {
    extern "C" {
        fn _machine_start_trap();
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct MachineTrapFrame {
    pub registers: [u32; 32],
}

/// Exception (trap) handler in rust.
/// Called from the asm/asm.S
#[link_section = ".trap.rust"]
#[export_name = "_machine_start_trap_rust"]
pub extern "C" fn machine_start_trap_rust(_trap_frame: *mut MachineTrapFrame) -> usize {
    {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

/// Generic helper for triggering a custom CSR instruction.
/// Arguments:
/// * csr – the CSR address (e.g., 0x7ca)
/// * arg0 – first argument passed in x10 (a0)
/// * arg1 – second argument passed in x11 (a1)
/// * arg2 – third argument passed in/out via x12 (a2)
///
/// # Safety
/// You must ensure that the arguments are valid pointers or values expected by the CSR.
/// The behavior depends on which precompile you are triggering.
#[inline(always)]
fn csr_trigger_delegation(
    input_a: *mut u32,
    input_b: *const u32,
    round_mask: &mut u32,
) {
    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7ca, x0",
            in("x10") input_a.addr(),
            in("x11") input_b.addr(),
            inlateout("x12") *round_mask,
            options(nostack, preserves_flags)
        )
    }
}
// Your Rust code: 
#[repr(C)]
#[repr(align(32))]
pub struct U256(pub [u32; 8]);


const MODULUS: u32 = 1_000_000_000;


unsafe fn workload() -> ! {
    // a and b are two 256-bit buffers (8×u32).
    // a is mutable because the delegated operation is expected to modify it in place. 
    // b is read-only input data for that operation. 
    let mut a = U256([1, 2, 3, 4, 0, 0, 0, 0]);
    let b = U256([6, 1, 0, 0, 126, 0, 0, 0]);
    let mut round_mask = 1;
    csr_trigger_delegation( a.0.as_mut_ptr(), b.0.as_ptr(), &mut round_mask );

    // deliver the result back to the host
    zksync_os_finish_success(&[a.0[0], a.0[1], a.0[2], a.0[3], a.0[4], a.0[5], a.0[6], a.0[7]]);
}

#[inline(never)]
fn main() -> ! {
    unsafe { workload() }
}
```

### Why this setup is required

- **Bare‑metal environment**: There is no `std` and no OS. The tiny assembly sets the stack pointer, clears/initializes memory regions, and jumps into `_start_rust`. Without it, your code would not have a valid entry point or stack.
- **Deterministic entry**: AirBender simulator/prover needs a deterministic, simple entry point so the execution trace is reproducible for proving.
- **Exit convention**: The prover/simulator reads registers `x10..x17` on exit. The helper `zksync_os_finish_success(&[u32; 8])` writes your eight outputs into those registers and halts in the expected way.

##  Producing outputs (the exit convention)

On success, write exactly eight words to `x10..x17` and set to zero `x18..x25`. Always use the following structure:

```rust
use riscv_common::zksync_os_finish_success;

let outputs = [w0, w1, w2, w3, w4, w5, w6, w7];
zksync_os_finish_success(&outputs);
```

The CLI `run` command prints these values for you to verify the program's behavior before proving.

## Building and running

From your example directory (e.g., `examples/big_int/`):

```bash
#!/bin/sh
rm app.bin
rm app.elf
rm app.text

cargo build --release # easier errors
cargo objcopy --release -- -O binary app.bin
cargo objcopy --release -- -R .text app.elf
cargo objcopy --release -- -O binary --only-section=.text app.text
```

Run the binary in the RISC-V simulator from the repository root:

```bash
cargo run --profile cli --package cli -- run --bin examples/big_int/app.bin
```

Useful flags:
- `--cycles N` to limit cycles.
- `--machine {standard|reduced|reduced-final|reduced-log23}` to select the machine configuration.
- `--input-file path.txt` to provide input when your program reads from the CSR oracle.

### Note

Delegations are ABI‑specific. Some use indirect memory access via pointers in `x10`/`x11`, and may modify certain registers, for example, when writing status back to `x12`. Before calling a delegation, check its ABI to confirm which registers are indirect or direct, and whether they are read-only or read-write.
See the Delegation Circuits guide for per‑delegation details: [Delegation circuits](./delegation_circuits.md).


In practice, your program uses the main circuit for overall logic and calls delegations for the heavy cryptographic or big‑integer pieces. When testing, first run with the CLI `run` command to confirm outputs, then move on to proving as described in [End-to-end guide](./end_to_end.md).
