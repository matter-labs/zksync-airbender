
/-! # What a reader of this spec must trust

Everything the final theorems (`Human/Theorems.lean`, `HumanSail/Theorems.lean`, `Human/DelegationRuns.lean`) claim is
stated in `human/`, in terms of the libraries listed here; `verify.sh` checks this (no statement depends on a
definition from `slop/`; `human/` imports only these libraries; every proof uses only the standard axioms; no
`sorry` anywhere, enforced by the build).

1. **Lean**: the Lean 4 kernel (the toolchain pinned in `lean-toolchain`) and its three standard axioms `propext`,
   `Classical.choice`, `Quot.sound`. `backup-check.sh` re-checks every declaration with a second kernel, by hand every
   few months at most.
2. **Mathlib** (pinned in `lakefile.toml`): `ZMod`, `Fin` vectors, finite sums, `AdjoinRoot`, used to state the
   field arithmetic of the specs.
3. **The Sail RISC-V model** (`SailRV32`, generated from the official `sail-riscv` at the commit pinned in
   `sail/PINS.md`, with Airbender's config `sail/config/`) and the `lean-sail` library it runs on (`Sail`, pinned in
   `sail/fetch-lean-sail.sh`, with the patches in `sail/patches/`).
4. **The images** (`Image`, `ImageMop`): the guest binaries' bytes as Lean data. `verify.sh` rebuilds the binaries and
   checks the images equal them.
5. **Transcriptions of standards** in `human/`: Blake2s (RFC 7693), Keccak-f[1600] (FIPS 202); `Human/Vectors.lean`
   states that they give the standards' test vectors (proven).
6. **Airbender facts** in `human/` (its decoder table, its changes to Sail, its precompiles), taken from Airbender's
   sources as cited at each definition (`docs/airbender-notes.md`).

Proof-search code (tactics) may evaluate terms with `unsafe` code or loop with `partial` functions. It is not trusted:
the kernel re-checks everything it produces. It is confined to the modules listed in `tacticModules`. -/

namespace Trust
open Lean

/-- The libraries `human/` imports and its statements are stated in (module name prefixes), besides `human/`
itself. -/
def libraries : List Name :=
  [`Init, `Mathlib, `SailRV32, `Sail, `Image, `ImageMop]

/-- The spec's own modules. -/
def spec : List Name := [`Human, `HumanSail]

/-- Proof-search modules allowed to contain `unsafe` or `partial` code (never part of a statement or proof term). -/
def tacticModules : List Name :=
  [`Slop.Sym.Meta, `Slop.Block.ParSym, `Slop.RV.Tactic, `Slop.Equiv.Run, `Slop.Equiv.Walk, `Slop.Equiv.MemLemmas]

end Trust
