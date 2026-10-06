# Upstream Sail RV32 reference

This directory holds generated reference artifacts, not handwritten ISA semantics.
This README and `provenance.json` are local documentation/metadata; the `.lean`
files are upstream compiler output and copied backend support. See
[trust and review boundaries](../../TRUST_AND_REVIEW.md) for what remains unchecked.

The instruction semantics come from **riscv/sail-riscv**, not from a local rewrite
of ADD, SUB, or ADDI. The source review entry is
[`base_insts.sail`](../../vendor/sail-riscv/source/model/extensions/I/base_insts.sail):
the `ITYPE` execution clause implements ADDI and the `RTYPE` clause implements
ADD and SUB. The register accessors are in
[`regs.sail`](../../vendor/sail-riscv/source/model/core/regs.sail).
These files are unmodified upstream snapshots; they are not a standalone Sail project.

| Component | Pinned revision |
| --- | --- |
| [RISC-V model](https://github.com/riscv/sail-riscv) | `bf32036e9aea614298e3ccf32d7a33d71ddc7c1b` |
| [Sail compiler](https://github.com/rems-project/sail), 0.20.3 | `3df54034910b31a1e00d948ee965b2e9603d68e0` |
| [Lean Sail runtime](https://github.com/rems-project/lean-sail), v6 | `c816ea7ad03cce98d51acee252540fd4215fede8` |

`rv32d_v256_e32.json` is the upstream CMake-generated configuration with
**XLEN = 32**, not the documented RV64 emulator example. Selection of the
upstream `I_insts` module and dependency pruning restrict this snapshot to the
`execute_RTYPE` and `execute_ITYPE` roots and their transitive dependencies.
This is not coverage of every instruction in the configuration.

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
It implements no instruction arithmetic or register semantics. Single-file
output avoids the backend's include-file bookkeeping failure on a pruned model.
Compare the regenerated Lean files before replacing a checked-in snapshot.

The model-to-Lean translation and pruning remain a trust boundary. Lean checks
proofs about the generated definitions; that does not certify the Sail compiler.
The runtime is reused as a pinned Lake dependency, including its effect semantics
and sequential interpreter. Source model licensing is in
[`LICENCE`](../../vendor/sail-riscv/LICENCE); compiler support licensing is in
[`SAIL_COMPILER_LICENSE`](SAIL_COMPILER_LICENSE).
