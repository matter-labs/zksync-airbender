# Pins (everything `sail/regen.sh` consumes)

| What | Pin | Notes |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.34.1` | latest stable at time of writing (2026-10-12) |
| Sail compiler | `rems-project/sail` @ `2ba321281cea18485f783da05c8a147a45d6b980` | prints `Sail 0.20.3 (sail2 @ 2ba3212)`; HEAD of `sail2` on 2026-10-12 (2026-10-09 commit "Apply --lean-line-width to all definition files"). sail-riscv requires version `0.20.3` (`cmake/sail_required_version.txt`). Built with opam switch `sail` (OCaml 5.4.1). |
| sail-riscv | `riscv/sail-riscv` @ `6136f84326f41dbaf72daf43a3787195ea3bd1c6` | = tag `2026-10-12-6136f84` = `master` on 2026-10-12. The last stable release `0.15` (`549e723`, 2026-10-06) differs only in `V/vext_mem_insts.sail`, `V/vext_utils_insts.sail` and `prelude/prelude.sail` (the latter: "Simplify prelude binding for truncating division and modulus", used by DIV/REM). |
| lean-sail | `rems-project/lean-sail` @ `c816ea7ad03cce98d51acee252540fd4215fede8` | tag `v6` (2026-09-18), upstream toolchain v4.29.0. Vendored into `lean/sail-rv32/lean-sail/` with `patches/lean-sail-lean4.34.1.patch` applied. |
| z3 | 5.1.0 (any recent z3 works; only used by Sail's `--memo-z3` constraint solving) | `~/.local/bin/z3` here |
| Sail config | `sail/config/airbender-base.json` | stock sail-riscv RV32 config (`sail/config/rv32.json`) with CLINT, test interrupt generator and Zicntr off (see README); all other Airbender settings are made in Lean. Copy in the package: `airbender-base.json`. |

Patches (all under `sail/patches/`, applied in order by `regen.sh`):

* `sail-riscv-lean-missing-externs.patch`: three `val ... = {cpp: ...}` hooks (`event_csr_write_callback`,
  `event_callback`, `validate_event_selectors`) have no Lean implementation upstream at this commit, so the generated Lean
  does not compile (`Unknown identifier`). The patch gives each a trivial Sail body, exactly like the neighbouring
  `tlb_*_callback` / `ptw_*_callback` hooks already do (`function f(_) = ()`); `validate_event_selectors` returns `true`.
  None of them are reachable from instruction semantics except `event_callback` (a no-op trace hook).
* `lean-sail-lean4.34.1.patch`: Lean 4.29 -> 4.34 compatibility for lean-sail (`Sail/ArchSem.lean`,
  `Sail/ArchSemSequential.lean`, `lean-toolchain`).

Post-processing of generated code (in `regen.sh`): `assert c "msg"` -> `«assert» c "msg"` (identifier quoting only);
`set_option backward.do.legacy true` in `RvfiDii.lean` only (build-time workaround, see README).

Generation flavour: `SCOPE=full` (`--all-modules`), `VARIANT=proof`; see README.md for the alternatives and why.
