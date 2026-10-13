# sail/ -- regenerating the Sail RISC-V RV32 Lean model

`sail/regen.sh` rebuilds `lean/sail-rv32/` from scratch from pinned sources (see `PINS.md`):

1. (optional `--bootstrap-sail`) builds the pinned Sail compiler in an opam switch (`opam install . --deps-only`,
   `make install`). Without the flag it only checks that `sail` on PATH (or `~/.opam/sail/bin`) is exactly
   `Sail 0.20.3 (sail2 @ 2ba3212...)` and that `z3` is on PATH. The bootstrap branch was not re-run end to end here
   (the installed compiler was built from the same commit with the same steps).
2. shallow-fetches `riscv/sail-riscv` at the pinned commit and applies `patches/sail-riscv-*.patch`;
3. shallow-fetches `rems-project/lean-sail` at the pinned commit and applies `patches/lean-sail-*.patch`;
4. runs `sail --lean` with upstream's flags (taken from sail-riscv's `model/CMakeLists.txt`) and `config/airbender-base.json`;
5. post-processes (two mechanical edits, see below), assembles the Lake package `lean/sail-rv32/`
   (`lakefile.toml`, `lean-toolchain` = v4.34.1, `SailRV32/*.lean`, vendored `lean-sail/`, `airbender-base.json` (the config the model was generated with),
   `PROVENANCE.txt`, `SailRV32Smoke.lean`).

Cold run: ~3.5 min, 1.3 GB RSS (with the Airbender config: 3:27). The output is byte-identical between runs (checked). `lake build` of the result:
4.3-4.5 min wall, 4.8 GB peak RSS, 16 cores, 146-148 jobs, no errors.

Why lean-sail is vendored (not a git `require`): the Lean 4.34 patch is ours, so a git require would need our own
fork or a patch step on every `lake update`; vendoring keeps `lake build` offline and reproducible. It is ~110 KB.

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

### Patches and mechanical edits
* `patches/sail-riscv-lean-missing-externs.patch`: upstream HEAD (and release 0.15) declares three `val`s with only a
  `cpp:` extern (`event_csr_write_callback`, `event_callback`, `validate_event_selectors`) and no Sail body, so the
  generated Lean has "Unknown identifier" and does not compile at all, even `--all-modules`. We give them the same trivial
  bodies as the neighbouring `tlb_*_callback`s (`()` / `true`). Report upstream.
* `patches/lean-sail-lean4.34.1.patch`: Lean 4.29 -> 4.34 (two small fixes in `ArchSem*.lean`, toolchain bump).
* `assert c "msg"` -> `«assert» c "msg"` in generated code (Lean 4.34 no longer resolves the bare identifier).
* `set_option backward.do.legacy true` in `RvfiDii.lean` only: with 4.34's new `do` elaborator `print_rvfi_exec` (an
  RVFI trace printer) needed > 17 min and 13 GB; with the legacy elaborator 1 s. Not used by the ISA semantics.

### Smoke test
`cd lean/sail-rv32 && lake build SailRV32Smoke`: config-independent checks with `decide +kernel` from Sail's reset state
(decode ADD/MUL, one `try_step` running ADD in the stock main memory at 0x80000000). The Airbender machine's checks are in
`lean/human/Human/Config.lean`.
