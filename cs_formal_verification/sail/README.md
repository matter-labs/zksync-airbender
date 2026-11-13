# sail/ -- regenerating the Sail RISC-V RV32 Lean model

`sail/regen.sh` rebuilds `lean/sail-rv32/` from scratch from pinned sources (see `PINS.md`):

1. (optional `--bootstrap-sail`) builds the pinned Sail compiler in an opam switch (the exact versions in `opam-packages.txt`,
   `make install`). Without the flag it only checks that `sail` on PATH (or `~/.opam/sail/bin`) is exactly
   `Sail 0.20.3 (sail2 @ 2ba3212...)` and that `z3` is on PATH. The bootstrap runs end to end in the CI container
   (ubuntu:24.04, apt `opam` 2.1.5 and `z3` 4.8.12; `ci/lean-ci.sh sail-gen`): the generated `SailRV32` tree is
   byte-identical to the one generated on macOS. The fetched commit is checked out as branch `sail2`, because Sail's
   version string names the branch (a detached checkout prints `HEAD @ ...` and fails the check).
2. shallow-fetches `riscv/sail-riscv` at the pinned commit and applies `patches/sail-riscv-*.patch`;
3. fetches lean-sail with `fetch-lean-sail.sh` (pinned commit + `patches/lean-sail-*.patch`);
4. runs `sail --lean` with upstream's flags (taken from sail-riscv's `model/CMakeLists.txt`) and `config/airbender-base.json`;
5. post-processes (three mechanical edits, see below), assembles the Lake package `lean/sail-rv32/`
   (`lakefile.toml`, `lean-toolchain` = v4.35.0, `SailRV32/*.lean`, `lean-sail/` (fetched, never committed), `airbender-base.json` (the config the model was generated with),
   `PROVENANCE.txt`, `SailRV32Smoke.lean`).

Cold run: ~3.5 min, 1.3 GB RSS (with the Airbender config: 3:27). The output is byte-identical between runs (checked). `lake build` of the result:
4.3-4.5 min wall, 4.8 GB peak RSS, 16 cores, 146-148 jobs, no errors.

lean-sail is NOT committed: upstream has no licence, so this public repo must not carry a copy. `fetch-lean-sail.sh`
(called by `verify.sh`, `lean/check.sh` and `regen.sh`) fetches the pinned commit into the gitignored
`lean/sail-rv32/lean-sail/` and applies our patch; it is a no-op when that copy is already current (stamp file
`.fetched` = commit + patch hash). Not a git `require`, because the Lean 4.35 patches are ours.

## Choices

### Module scope: everything (`SCOPE=full`, default)
`--all-modules`, as upstream's CMake does. The whole RV32 model builds fine (174 generated files, 51 MB, 4.5 min,
4.8 GB peak), so no restriction is needed. We tried a short list (`SCOPE=min`: `main I_insts M_insts Zicsr_insts`,
which still drags in F/D/H/A/Zicbom/Zicfilp/Sdtrig through `postlude`'s `requires`; 135 files, 11 MB, 2 min, 2.3 GB)
and rejected it: scattered functions such as `currentlyEnabled` have one clause per extension in the extension's own
module, so omitting modules leaves `currentlyEnabled` partial (44 of 139 `extension` constructors unmatched: B, Zb*, Zk*,
Zicond, Zihintpause, Zimop, V crypto, ...). Sail only warns, and the Lean model then fails at run time
(`init_model` -> "Pattern match failure at extensions/Zicboz/zicboz_insts.sail" while resetting misa). riscv-zkvm works
around this with an "omitted is disabled" rewrite of the fallback arm and extra modules; we avoid editing semantics.
With `SCOPE=full` there are no incomplete-match warnings from Sail and `currentlyEnabled` is total.
Filtering of unwanted instructions (CSR, FENCE, A, C, F/D, ...) is therefore left to our glue code, as intended.

### Variant (`VARIANT=proof`, default)
| VARIANT | flags | custom axioms | `#eval` | works with SCOPE=full |
|---|---|---|---|---|
| `default` | upstream default: `--lean-noncomputable`, `encdec_*` noncomputable, hooks = `axiom` (`RiscvExtras.lean`) | 75 (see below) | no | yes |
| `proof` | as `default` but hooks are concrete panicking defs (`RiscvExtrasExecutable.lean`) | none | no | yes |
| `executable` | upstream executable flags: nothing noncomputable, code is generated | none | yes | **no** (Lean IR tag limit: `instruction` has > 256 constructors; builds only with SCOPE=min) |

`default`'s axioms (all in `RiscvExtras.lean`): `plat_term_read/write`, `load/match/cancel/valid_reservation`,
`get_16_random_bits`, `sys_enable_experimental_extensions`, and ~65 `riscv_f{16,32,64}*` softfloat functions.
`try_step`, `execute`, `encdec_backwards`, `ext_decode`, `sail_model_init` all depend on some of them in `default`
(e.g. `encdec_backwards` on `sys_enable_experimental_extensions`; `try_step` additionally on `valid_reservation`,
`plat_term_write`, softfloat), which makes kernel evaluation of decode/step get stuck. In `proof` those are definitions
(`valid_reservation _ := false`, `sys_enable_experimental_extensions _ := false`, `panic` for the others, unreachable for
RV32IM) and `try_step`, `execute`, `ext_decode`, `encdec_backwards`, `currentlyEnabled`, `sail_model_init` depend only
on `propext`, `Classical.choice`, `Quot.sound` (`execute_RTYPE`: `propext`, `Quot.sound`).
Everything is `noncomputable` in `proof`/`default`, but that does not matter for the kernel: `decide +kernel` evaluates
`ext_decode` and a whole `try_step` (see `SailRV32Smoke.lean`; plain `decide` gets stuck on the well-founded
`hartSupports`/`currentlyEnabled`, `decide +kernel` does not). lean-sail's `SequentialState` (hash maps) is NOT
kernel-evaluable; the smoke test defines a function-based state (`FState`) and interpreter for that reason.

### Config (`config/airbender-base.json`; stock: `config/rv32.json`)
The config is baked in at Sail -> Lean generation time (`sail --config`: every `config a.b.c` becomes a constant, register
initialisers become values); `init_model ""` validates it at run time (`config_is_valid`) and resets.

Policy: **all Airbender choices live in Lean** (`lean/human/Human/Airbender.lean`: misa = I+M, memory map with misaligned
faults, instruction/CSR whitelist), where they can be reviewed and changed without regenerating. The JSON differs from
stock only where Lean cannot help (`diff rv32.json airbender-base.json`, marked `// AIRBENDER`):
* CLINT off and the test interrupt generator off: their stock MMIO addresses (0x2000000, 0xC000000) lie inside Airbender's
  RAM [2M, 1G) and Sail routes those addresses to the devices before looking at the PMA list.
* Zicntr off: `config_is_valid` requires a time source (the CLINT) for it. Its instructions are CSR reads, which the Lean
  whitelist rejects anyway.
* Zihintntl, Zicbop off: they re-decode base instructions Airbender runs as plain RV32I (`add x0, x0, x2..x5` -> NTL,
  `ori x0, rs1, imm` -> PREFETCH). Whether an extension is on is a compile-time constant (`hartSupports`), so Lean
  cannot switch it off. Zicfilp, Zicfiss off: landing-pad / shadow-stack checks in JALR and the step. Zca (and Zcb,
  Zcf, Zcd, Zcmop, which need it) off: no compressed instructions, so 2-byte-aligned jump targets trap, as in Airbender.
  Other extensions stay as stock: `Human/ISA/Sail/Airbender.lean`'s `Supported` rejects their instructions. (Switching
  every extension off fails `config_is_valid`: PMA attributes, `physaddr_bits`, FS/vector settings depend on them.)

### Patches and mechanical edits
* `patches/sail-riscv-lean-missing-externs.patch`: upstream HEAD (and release 0.15) declares three `val`s with only a
  `cpp:` extern (`event_csr_write_callback`, `event_callback`, `validate_event_selectors`) and no Sail body, so the
  generated Lean has "Unknown identifier" and does not compile at all, even `--all-modules`. We give them the same trivial
  bodies as the neighbouring `tlb_*_callback`s (`()` / `true`). Report upstream.
* `patches/lean-sail-lean4.35.0.patch`: Lean 4.29 -> 4.35 (two small fixes in `ArchSem*.lean`, toolchain bump).
* `patches/lean-sail-skip-inductive-codegen.patch`: adds `Sail/SkipCodegen.lean`, the `skip_inductive_codegen` command
  wrapper. Since Lean 4.35, declaring an inductive type computes each constructor's runtime layout and rejects a
  data-carrying constructor whose tag exceeds 243 (lean4#8930); `instruction` has 361. The wrapper runs the compiler's
  per-type phases but leaves the rejected constructors without a layout (4.34's behaviour). It touches only the
  compiler: the declarations sent to the kernel are unchanged (all 230 inductive types of `SailRV32.Defs` hash
  identically on 4.34.1 and 4.35.0), and the kernel and the replay checkers re-check every declaration, so it is not
  trusted. Remove it once lean4#8930 is fixed.
* `skip_inductive_codegen` inserted before `inductive instruction where` in `Defs.lean` (one line; see above).
  Consequence for proofs: `simp [f]` / `rw [f]` on a definition `f` that matches on `instruction` with a catch-all case
  builds a splitter, which Lean 4.35 compiles and which fails on the layout-less constructors ("`…` was not compiled");
  unfold with `f.eq_def` or `change` instead (e.g. `Proven.ISA.Equiv.StepMop`).
* `assert c "msg"` -> `«assert» c "msg"` in generated code (Lean 4.34 no longer resolves the bare identifier).
* `set_option backward.do.legacy true` in `RvfiDii.lean` only: with 4.34's new `do` elaborator `print_rvfi_exec` (an
  RVFI trace printer) needed > 17 min and 13 GB; with the legacy elaborator 1 s. Not used by the ISA semantics.

### Smoke test
`cd lean/sail-rv32 && lake build SailRV32Smoke`: config-independent checks with `decide +kernel` from Sail's reset state
(decode ADD/MUL, one `try_step` running ADD in the stock main memory at 0x80000000). The Airbender machine's checks are in
`lean/human/Human/ISA/Sail/Checks.lean`.

## Claims and licences

The generated model is committed with `PROVENANCE.txt`, `SAIL_COMPILER_LICENSE` and `SAIL_RISCV_LICENSE`.
CI regenerates it and checks the diff before it restores the Lake manifest.
The lean-sail runtime is fetched. Its upstream repository has no licence.
The existing `patches/lean-sail-*.patch` files contain upstream source lines.
The owner must refer these patches to Legal. Do not add source lines from lean-sail.

[Final ISA claims](../lean/proven/Proven/Final/ISA/) include the following results.
[Claims.lean](../lean/test/Checks/Claims.lean) records the type checks and axiom roots for all circuit and trace claims.

| Group | Final theorems |
| --- | --- |
| [DelegationRuns](../lean/proven/Proven/Final/ISA/DelegationRuns.lean) | `calls_run`, `blake_compress_run`, `blake_hash_run`, `blake_compress_run10`, `blake_hash_run10`, `blake_g_run`, `blake_g_run10`, `keccak_special5_run`, `keccak_f1600_run` |
| [Theorems](../lean/proven/Proven/Final/ISA/Theorems.lean) | `decode_is_sail`, `step_is_airbender`, `machine_checks_claim` |
| [Vectors](../lean/proven/Proven/Final/ISA/Vectors.lean) | `standard_vectors` |
| [WholeRun](../lean/proven/Proven/Final/ISA/WholeRun.lean) | `run_is_airbender`, `agree_exists`, `fetch_keeps_configured`, and their separate non-vacuity proofs |
| [MachineTargets](../lean/proven/Proven/Final/ISA/MachineTargets.lean) | `unrolled_full_unsigned_sail`, `unrolled_reduced_sail`, `unified_sail` |
| [NativeTargets](../lean/proven/Proven/Final/ISA/NativeTargets.lean) | `unrolled_full_from_native_sail`, `unrolled_reduced_from_native_sail`, `unified_from_native_sail` |

Decode, step and delegation-run soundness have separate non-vacuity statements.
The [claim inventory](../docs/VERIFICATION_STATUS.md) lists every final claim,
its proof and its non-vacuity statement or fixed-data boundary.

The Airbender machine uses its own definitions for loads into x0, `mop.rr.N`, `mop.r.N`, CSR `0x7c0` and delegations.
These effects are not Sail instruction effects.
