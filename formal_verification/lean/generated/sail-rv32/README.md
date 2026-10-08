# Upstream Sail RV32 reference

This directory holds generated reference artifacts, not handwritten ISA semantics.
This README and `provenance.json` are local documentation/metadata; the `.lean`
files are upstream compiler output and copied backend support, except the recorded
platform-parameter header in `SailRV32.lean` and
`SailRV32/SailPlatform.lean`: our platform configuration and runtime compatibility support,
copied through the backend's `--lean-import-file` option. See
[trust and review boundaries](../../TRUST_AND_REVIEW.md) for what remains unchecked.

The instruction semantics come from **riscv/sail-riscv**, not from a local rewrite
of ADD, SUB, or ADDI. The source review entry is
[`base_insts.sail`](../../vendor/sail-riscv/source/model/extensions/I/base_insts.sail):
the `ITYPE` execution clause implements ADDI and the `RTYPE` clause implements
ADD and SUB; `UTYPE` implements LUI and AUIPC. The original branch and JAL
clauses are in the same source; JALR is in
[`jalr_seq.sail`](../../vendor/sail-riscv/source/model/extensions/I/jalr_seq.sail).
`SHIFTIOP` retains the
original SLLI/SRLI/SRAI clause, including RV32 low-five-bit extraction. The original MUL/DIV/REM clauses are
in [`mext_insts.sail`](../../vendor/sail-riscv/source/model/extensions/M/mext_insts.sail).
The register accessors are in
[`regs.sail`](../../vendor/sail-riscv/source/model/core/regs.sail).
PC accessors and retirement assignment are in
[`pc_access.sail`](../../vendor/sail-riscv/source/model/core/pc_access.sail).
The normal four-byte nextPC assignment is in
[`step.sail`](../../vendor/sail-riscv/source/model/postlude/step.sail), `run_hart_active`'s
normal `F_Base` branch. These files are unmodified upstream snapshots; they are not
a standalone Sail project.

| Component | Pinned revision |
| --- | --- |
| [RISC-V model](https://github.com/riscv/sail-riscv) | `bf32036e9aea614298e3ccf32d7a33d71ddc7c1b` |
| [Sail compiler](https://github.com/rems-project/sail), 0.20.3 | `3df54034910b31a1e00d948ee965b2e9603d68e0` |
| [Lean Sail runtime](https://github.com/rems-project/lean-sail), v6 | `c816ea7ad03cce98d51acee252540fd4215fede8` |

`rv32d_v256_e32.json` is the upstream CMake-generated configuration with
**XLEN = 32**, not the documented RV64 emulator example. Selection of the
upstream `I_insts` and `M_insts` modules, extracted PC helper and dependency pruning restrict this snapshot to the
`execute_RTYPE`, `execute_ITYPE`, `execute_BTYPE`, `execute_JAL`, `execute_JALR`,
`execute_REV8`, `execute_SHIFTIOP`, `execute_UTYPE`, `execute_MUL`, `execute_DIV`,
`execute_REM`, `execute_LOAD`, `execute_STORE`, `get_arch_pc`, `get_next_pc`,
`tick_pc`, `normal_base_next_pc` and `encdec_backwards` roots and their transitive dependencies.
This is not coverage of every instruction in the configuration.
The decoder retains the selected modules' original mapping clauses. Successful
decoding of the seven restricted instructions is checked in `Tests/SailDecoder.lean`.
The postlude's `ILLEGAL` fallback is excluded; decoding completeness and unsupported
instruction behavior are not claimed. No mapping clause is rewritten.
`Zicsr` is selected to retain its original `currentlyEnabled(Ext_Zicsr)` clause,
needed by JALR's landing-pad configuration query; no CSR-instruction proof is claimed.
Its unmodified source is in
[`zicsr_insts.sail`](../../vendor/sail-riscv/source/model/extensions/Zicsr/zicsr_insts.sail).
The generator copies the normal `F_Base` assignment verbatim into
[`extracted_base_pc.sail`](extracted_base_pc.sail); Sail generates the helper's Lean
body. The provenance records its source hash, branch, line and exact statement.
Our reference composes that helper, execution and `tick_pc`. The complete fetch,
interrupt and exception driver is outside this slice; extraction/path selection
are additional unchecked connections.

## Regeneration

Use clean checkouts at the revisions above. Install the compiler's build
dependencies in an OCaml switch and run from that switch with Dune and Z3 on PATH:

```sh
python3 scripts/generate_sail.py \
  --compiler-source /path/to/sail \
  --model-source /path/to/sail-riscv \
  --output /tmp/new-sail-rv32
```

The script verifies the checkout revisions and tracked source contents, builds
the original compiler and Lean backend plus `scripts/sail_slice.ml`, and records
the source pins and generated-file hashes in `provenance.json`. The small adapter
runs the upstream Lean backend's unmodified rewrite sequence, prunes unreachable
definitions with upstream callgraph analysis, and invokes its original emitter.
It implements no instruction arithmetic or register semantics. The generator
also verifies the pinned emulator's experimental-extension default and getter.
Our platform binding selects `false`, matching those sources; this does not claim
that every Sail platform uses that setting. The manifest records the binding and
source hashes. Other extension configuration queries retain the upstream clauses.
The same support file adds the missing runtime-error instance for early-return
computations. [Its proofs](../../Airbender/Proofs/Sail/Runtime.lean) establish error
propagation and agreement with Sail's native handler; no new effect model is added.
Terminal writes and reservation calls remain abstract through `MemoryPlatform`.
The generator inserts an implicit instance parameter and lifted aliases after
`namespace Functions`; it records the exact header and pre-insertion hash.
Removing that header reproduces the original emitter hash. No instruction body
is rewritten and no terminal/reservation behavior is assumed. Native memory claims
quantify over this parameter and state their access contracts explicitly.
The generator
mechanically extracts the PC assignment; its fidelity and selected-path scope need review. Single-file
output avoids the backend's include-file bookkeeping failure on a pruned model.
Compare the regenerated Lean files before replacing a checked-in snapshot.

The extraction, model-to-Lean translation and pruning remain a trust boundary. Lean checks
proofs about the generated definitions; that does not certify the Sail compiler.
The runtime is reused as a pinned Lake dependency, including its effect semantics
and sequential interpreter. Source model licensing is in
[`LICENCE`](../../vendor/sail-riscv/LICENCE); compiler support licensing is in
[`SAIL_COMPILER_LICENSE`](SAIL_COMPILER_LICENSE).
