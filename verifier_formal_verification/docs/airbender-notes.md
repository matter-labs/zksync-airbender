# Airbender guest-program notes (research for the Lean/Sail PoC)

Read: `matter-labs/zksync-airbender` @ `6ec4ea725d654c5e4fd3a122d571ca37804f9abd` (default branch, shallow clone)
and `matter-labs/zksync-os` @ `f91897ce4ff4ede1f8d338411d023645684d0fb7` (main guest).
Paths below are relative to the respective repo root. No separate sdk/platform repo was needed;
`riscv_common` (in the airbender repo) is the guest-side "SDK".

## 1. ISA / execution environment

Sources: `docs/simulator_supported_instructions.md`, `docs/machine_configuration.md`,
`docs/philosophy_and_logic.md`, `risc_v_simulator/src/cycle/{mod.rs,state.rs}`, `tools/cli/src/main.rs`.

- Base machine for ZKsync OS and for our purpose: **"standard" = RV32IM, machine mode only, no
  exceptions**. CLI: `Machine::Standard` -> `IMStandardIsaConfig` (`risc_v_simulator/src/cycle/mod.rs`):
  `SUPPORT_MUL/DIV/SIGNED_MUL/SIGNED_DIV/SIGNED_LOAD/LOAD_LESS_THAN_WORD/SRA = true`,
  `SUPPORT_MOPS=false`, `HANDLE_EXCEPTIONS=false`, `SUPPORT_ONLY_CSRRW=true`.
- RV32I: all of LUI AUIPC JAL JALR, 6 branches, LB LH LW LBU LHU SB SH SW, all imm/reg ALU ops, shifts
  (SLL SRL SRA, SLLI SRLI SRAI), SLT[U][I]. RV32M: MUL MULH MULHSU MULHU DIV DIVU REM REMU
  (docs: "The operations in the RV32M extension are among the most complex to encode").
- NOT supported (decoder marks invalid; trusted-code => proof unsatisfiable): FENCE/FENCE.I
  ("nothing to do in fence, our memory is linear"), ECALL, EBREAK, MRET, WFI, A extension
  (explicit `IllegalInstruction`), compressed (C) — not in the decoder, programs are 4-byte aligned
  (`ASSERT(ORIGIN(REGION_TEXT) % 4 == 0)`), all CSR ops other than CSRRW. (Older simulator; the current
  riscv_transpiler accepts every Zicsr form on CSR 0x7c0: source 0 reads, rd = x0 is a no-op write.)
  Zimop/MOP only in reduced/recursion machines (`IMIsaConfigWithAllDelegations`,
  `IWithoutByteAccess*`), used for Mersenne31 `mop.rr.{0,1,2}` add/sub/mul — not in `Standard`.
- "Reduced" machines (`IWithoutByteAccessIsaConfig*`): no MUL/DIV/byte access; recursion only, irrelevant.
- Misaligned: "Unaligned accesses are disallowed by design ... relying on the compiler" and "all
  inefficient unaligned full-word memory accesses and odd half-word accesses" are disallowed
  (`docs/machine_configuration.md`, `docs/philosophy_and_logic.md`). Hence guest flag
  `-unaligned-scalar-mem`. Docs also list "divide-by-zero forbidden" as an invariant (avoid DIV/REM).
- Traps: none modelled. Circuit: `ASSUME_TRUSTED_CODE=true`, `OUTPUT_EXACT_EXCEPTIONS=false`; any
  illegal instr / misaligned access / fetch outside ROM (ROM padded with UNIMP) => unsatisfiable.
  Simulator (`state.rs` ~L1504): `if Config::HANDLE_EXCEPTIONS == false { panic!("Simulator encountered an exception") }`.
  Guest still ships a trap handler (`asm_reduced.S` `machine_default_start_trap`, uses
  csrrw mscratch/csrw mepc/mret) but it is never reachable in the standard machine and `_setup_interrupts`
  never writes mtvec. The PoC should NOT include it.
- Memory: ROM `[0, 2M)` holds code+rodata, fetched via fixed table; RAM `[2M, 1G)` (2^30 bytes total
  address space, "addresses are 30-bit values"). Registers live in "RAM with is_register tag".
  PC starts at 0 (`entry_point: 0` in `tools/cli/src/main.rs` `run_binary`).
- CSRs (only CSRRW; `state.rs`):
  - `0x7c0` NON_DETERMINISM_CSR: the oracle/input channel. `csrrw rd,0x7c0,x0` reads next word,
    `csrrw x0,0x7c0,rs` writes a word (also used by QuasiUART debug printing).
  - `0x7c7` (1991) blake2s round w/ extended control; `0x7ca` (1994) u256 bigint ops — delegation
    precompiles, args via pointers in x10..x13 (`risc_v_simulator/src/delegations/`). Docs also
    mention `0x7ff` MARKER_CSR (simulator only).
  - machine CSRs mstatus/mtvec/mepc/... exist only in the (unused) HANDLE_EXCEPTIONS path.
  - `csrrw x0, cycle(0xC00), x0` is deliberately an unimplemented CSR = "finish error"
    (`riscv_common::zksync_os_finish_error`) -> unsatisfiable / assertion in simulator.
- Termination: simulator stops when `pc` is unchanged after a cycle (`risc_v_simulator/src/sim/mod.rs`:
  `if self.machine.state().pc == previous_pc { end_of_execution_reached = true; ...}`), i.e. a
  self-jump `jal x0, 0` (`0x0000006f`), which is what `loop { continue; }` compiles to. Output
  convention: final values of **x10..x17** (8 words), x18..x25 zeroed ("our convention for
  recursive chain start"); x10-x25 are the public output.

## 2. Build pipeline (guest)

Files: `rust-toolchain.toml`, `examples/*/.cargo/config.toml`, `examples/*/Cargo.toml`,
`examples/*/dump_bin.sh`, `examples/scripts/lds/{memory.x,link.x}`, `examples/scripts/asm/asm_reduced.S`;
for the OS: `zksync-os/zksync_os/{.cargo/config.toml,Cargo.toml,dump_bin.sh,rust-toolchain.toml,src/lds}`.

- Toolchain: nightly. airbender repo `channel = "nightly-2025-07-25"`; zksync-os `nightly-2026-01-22`.
  Guests use `#![feature(allocator_api)]`, `generic_const_exprs` (not really needed).
  Setup: `rustup target add riscv32i-unknown-none-elf`, `llvm-tools-preview`, `cargo-binutils` (`cargo objcopy`).
- Target: stock **`riscv32i-unknown-none-elf`** (no custom JSON), M enabled by feature flag.
  `examples/basic_fibonacci/.cargo/config.toml` (identical for all examples):
  ```
  [build] target = "riscv32i-unknown-none-elf"
  rustflags = ["-C","target-feature=+m,-unaligned-scalar-mem,+relax",
    "-C","link-arg=-T../scripts/lds/memory.x","-C","link-arg=-T../scripts/lds/link.x",
    "-C","link-arg=--save-temps","-C","force-frame-pointers"]
  ```
  (`experiments` adds `+zimop`.) zksync-os adds `-C codegen-units=1`, `--remap-path-prefix`, `--build-id=sha1`.
  Note `+relax` = linker relaxation ON (auipc+jalr -> jal, gp-relative via `__global_pointer$`);
  `force-frame-pointers` => s0/fp frame setup in every non-leaf fn (see `sw ra,12(sp); sw s0,8(sp); addi s0,sp,16`
  in `examples/basic_fibonacci/app.bin`). No `-C relocation-model` flag (target default static),
  no `--no-relax`, no `-C panic` flag.
- Profiles: examples: only `[profile.release] lto = true` (opt-level default 3, panic abort is the
  none-target default). zksync_os: `opt-level=3, lto=true, codegen-units=1, panic="abort", debug=true`.
- Linker script memory map (`examples/scripts/lds/memory.x`):
  `ROM (rx) ORIGIN=0 LENGTH=2M`, `RAM (rwa!x) ORIGIN=2M LENGTH=1022M`; TEXT/RODATA/DATAINIT -> ROM;
  STACK/DATA/BSS/HEAP -> RAM. `link.x` (riscv-rt derived): `_stext=0`, `_hart_stack_size=64M`,
  `_heap_size=768M`; `.text` first has `*(.init)`, `*(.init.rust)`, `.trap`, `.trap.rust`, then `.text.*`;
  then `.rodata` (ROM), `.stack` at RAM start (`_estack` = 2M, `_sstack` = 2M+64M, SP starts at top
  `_sstack`), `.data`, `.bss`, `.heap`. `ASSERT(SIZEOF(.data)==0)`: **no initialised mutable statics**;
  `.got` must be empty. (zksync-os variant places `.rodata` in RAM with init image in ROM.)
- Entry (`examples/scripts/asm/asm_reduced.S`): `_start` at address 0:
  `la ra,_abs_start; jr ra` ; `_abs_start`: `.option norelax; la gp,__global_pointer$`;
  `la sp,_sstack`; `add s0,sp,zero`; `jal zero,_start_rust`. `_start_rust` (Rust,
  `#[link_section=".init.rust"] #[export_name="_start_rust"] unsafe extern "C" fn start_rust() -> !`) calls `main()`.
  No bss/data init (RAM is guaranteed zero; no .data allowed).
- Input: `riscv_common::csr_read_word()` = `csrrw {rd}, 0x7c0, x0` (inline asm, `options(nomem,nostack,preserves_flags)`).
  CLI `run --input-file` feeds a `QuasiUARTSource` oracle queue. Examples: `dynamic_fibonacci`
  reads `n`; `hashed_fibonacci` reads `n`,`h`. `basic_fibonacci` reads nothing.
- Output/termination: `zksync_os_finish_success(&[u32;8]) -> !` (`riscv_common/src/lib.rs`): copies to a
  `[u32;16]`, `black_box` pointer into x26, `lw x10..x25, 0..60(x26)` via inline asm, then
  `loop { continue; }` (= `jal x0,0`).
- Image: `cargo build --release`; `cargo objcopy --release -- -O binary app.bin` (flat ROM+data image
  loaded at 0; this is what the prover/CLI consumes: `cli run --bin app.bin`, `generate-vk --bin app.bin`);
  `app.text` = `-O binary --only-section=.text` (embedded by `execution_utils/src/lib.rs`
  for hashed_fibonacci); `app.elf` = objcopy `-R .text`. Committed `examples/*/app.bin` (basic_fibonacci
  is 388 bytes) are real artifacts we can compare against.

## 3. Representative examples (`examples/`)

`examples/basic_fibonacci/src/main.rs` (whole shape, ~80 lines):
```rust
#![no_std] #![allow(incomplete_features)] #![feature(allocator_api)]
#![feature(generic_const_exprs)] #![no_main] #![no_builtins]
use riscv_common::zksync_os_finish_success;
extern "C" { static mut _sheap: usize; static mut _eheap: usize;
             static mut _sstack: usize; static mut _estack: usize; }
core::arch::global_asm!(include_str!("../../scripts/asm/asm_reduced.S"));
#[no_mangle] extern "C" fn eh_personality() {}
#[link_section = ".init.rust"] #[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! { main() }
#[export_name = "_setup_interrupts"] pub unsafe fn custom_setup_interrupts() { ... }
#[link_section = ".trap.rust"] #[export_name = "_machine_start_trap_rust"]
pub extern "C" fn machine_start_trap_rust(_f: *mut MachineTrapFrame) -> usize { unsafe { core::hint::unreachable_unchecked() } }
unsafe fn workload() -> ! { let (mut a, mut b) = (1,1);
  for _i in 0..10 { let c = a + b; a = b; b = c; }
  zksync_os_finish_success(&[b,0,0,0,0,0,0,0]); }
#[inline(never)] fn main() -> ! { unsafe { workload() } }
```
`dynamic_fibonacci`: `let n = csr_read_word(); ... (a + b) % MODULUS` (u32 `%` => `remu`).
`hashed_fibonacci`: also drives blake2s via `csrrw x0,0x7c7,x0` with a `#[repr(align(65536))]` state struct;
`big_int`: `csrrw x0,0x7ca,x0`. `#![no_builtins]` is used in basic/dynamic_fibonacci, not in hashed_fibonacci.
Arithmetic is plain Rust; `black_box` only inside `zksync_os_finish_success_extended`.

## 4. Things that matter for verifying the compiled code

- Indirect calls / fn pointers: none in examples; zksync-os uses them freely; `jalr` is in the ISA.
- rodata: in ROM (examples) so `lui/addi` or gp-relative `lw` to ROM addresses; ROM reads via ordinary loads
  are allowed. PoC with only register arithmetic should have none.
- Global allocator: `riscv_common` installs `NullAllocator` (`unreachable_unchecked` on alloc) unless feature
  `custom_allocator`; no heap use in examples. Panic handler: `riscv_common` -> `rust_abort()` ->
  `zksync_os_finish_error()` (`csrrw x0,cycle,x0`; feature `custom_panic` disables it).
  Release has overflow checks off, so `a+b` wraps.
- u64 math: target has `+m`, so `u64` mul lowers inline to `mul`+`mulhu`(+`mul` cross terms); no
  `__muldi3` (only without M). u64 div/rem and 128-bit would call compiler_builtins (`__udivdi3`...).
- memcpy/memset: examples rely on compiler_builtins (hence `#![no_builtins]` on some); zksync-os supplies
  `memcpy.s`/`memset.s` via `global_asm!` (SP1/musl-derived, compiled `-march=rv32im`).
- Frame pointer: non-leaf fns save ra/s0 (`sw ra,12(sp)`), so the spec must handle stack stores/loads.

## 5. Mersenne31 in Airbender (mimic target)

`field/src/base.rs` (`Mersenne31Field(pub u32)`, `ORDER = (1<<31)-1`, repr(transparent)) with kernels in
`field/src/ops.rs`. Generic (non-riscv32) kernels — these are the pure-Rust forms to copy:
```rust
pub(crate) const fn add_mod(a: u32, b: u32) -> u32 {
    let mut sum = a.wrapping_add(b); let msb = sum & (1 << 31);
    sum ^= msb; sum += (msb != 0) as u32; sum }                  // result in 0..=ORDER (0 has 2 reprs)
pub(crate) const fn sub_mod(a: u32, b: u32) -> u32 {
    let mut sum = a.wrapping_sub(b); let msb = sum & (1 << 31);
    sum ^= msb; sum -= (msb != 0) as u32; sum }
pub(crate) const fn mul_mod(a: u32, b: u32) -> u32 {
    let product = (a as u64) * (b as u64);
    let product_low = (product as u32) & ((1 << 31) - 1);
    let product_high = (product >> 31) as u32;
    add_mod(product_low, product_high) }
```
`fma_mod(a,b,c)` = `mul_mod` then `add_mod` on riscv32.
Representation: non-canonical (<= ORDER); `to_reduced_u32` maps ORDER -> 0 (`PartialEq` compares reduced).
On riscv32 the crate requires feature `use_division` or `modular_ops`: `use_division` replaces the
carry trick with `remu x, sum, ORDER` via inline asm ("LLVM is a clever beast that does transform
`a % MODULUS` into multiplication ... want to inhibit"); `modular_ops` uses custom `mop.rr.0/1/2`
(not in the standard machine). So real guests use `remu`-based reduction in `zksync_os` hashing/circuits;
for the PoC the generic carry-trick form above is the most "Airbender-like" pure RV32IM code and avoids DIV.

## 6. Recommendation for our PoC crate

- Toolchain: pin a nightly that has the target installed. Locally installed (`~/.rustup/toolchains`):
  `nightly-2025-05-24` and `nightly-2025-09-04` have `riscv32i-unknown-none-elf` + `llvm-tools`
  (closest to airbender's `nightly-2025-07-25`); `1.99.0` has `riscv32im-unknown-none-elf`.
  Prefer `riscv32i-unknown-none-elf` + `-C target-feature=+m,-unaligned-scalar-mem,+relax`
  (exact airbender flags) with `rust-toolchain.toml = nightly-2025-09-04` (or install 2025-07-25).
  `riscv32im` also works (both ilp32, no C).
- `.cargo/config.toml`: same rustflags as airbender; link-args `-T memory.x -T link.x` copied
  verbatim from `examples/scripts/lds/` (or a minimal one: `.text` at 0 with `.init` first, `.rodata`
  after, stack top constant `_sstack = 2M+64M`, `/DISCARD/` eh_frame). Keep `force-frame-pointers`
  so the bytes match what Airbender produces.
- Cargo: `[profile.release] opt-level=3, lto=true, codegen-units=1, panic="abort", debug=false`;
  `#![no_std] #![no_main]`, no deps (do NOT depend on riscv_common; copy 2 small pieces instead).
- Entry: copy `_start` / `_abs_start` from `asm_reduced.S` (but drop the trap-handler section and
  `_setup_interrupts`); keep `la gp`, `la sp,_sstack`, `add s0,sp,zero`, `jal zero,_start_rust`.
- Termination: end with `loop {}` (compiles to `jal x0,0`); before it load results into x10.. (a0..) via
  the same `lw x10..` asm, or simply return value in a0 from `main`-like fn then `loop{}`. Note
  Airbender's convention x10..x17 = 8 output words, x18..x25 = 0. For the PoC: result in x10, rest 0.
- Inputs: Airbender reads via `csrrw rd,0x7c0,x0`. Sail's RISC-V model will treat `0x7c0` as a
  custom/unimplemented CSR, so for the PoC either (a) model CSR 0x7c0 reads as an oracle in Lean, or
  (b) simpler and recommended initially: pass the input as a precondition on a0 (register) / a memory
  word and state the theorem on that; document the difference. The functions
  `inc/double/combine` should be `#[inline(never)] extern "C"`/`pub extern "C" fn` taking/returning
  `u32` so rustc emits real `jal`/`ret` pairs (they would be inlined otherwise); `combine(x) = inc(x)+double(x)`
  with `wrapping_add`/`wrapping_shl` semantic (or Mersenne31 `add_mod`), call them from `workload()`.
- Polynomial: Horner `acc = fma(acc, x, c_i)` over Mersenne31 using the generic `add_mod`/`mul_mod` above
  on a `static COEFFS: [u32; 100]` (rodata in ROM; loads `lw` from ROM region) or fully unrolled with
  constants (`lui/addi`); `mul`+`mulhu` for the u64 product. Reduce with the carry trick (no DIV);
  optionally a second variant with `remu`-based reduction (Airbender `use_division`).
  Use `core::hint::black_box` on the input to prevent constant folding.
- Sail side: RV32, M on, C off, Zicsr only if modelling CSR 0x7c0; pc=0 start; treat `jal x0,0` as halt.
