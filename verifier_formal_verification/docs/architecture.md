# Proof architecture (decided 2026-10-12, after an architecture review)

## Trusted surface (what a human audits)
- `sail/` pins + `sail/config/airbender-rv32im.json` (diff vs stock) + `sail/patches/` (3 trivial externs, lean-sail 4.34 compat).
- `rust/` build flags + `rust/build.sh`; `verify.sh` checks `lean/image/Image.lean` == `build/app.bin`.
- `lean/human/` (~150 lines total):
  - `Machine.lean`: `SailState` (total-function regs/mem) + `runSail` (25-line interpreter of Sail's effect monad,
    mirrors lean-sail's `interpretSailEffects`) + `resetState` (= `sail_model_init; init_model`) +
    `step s := runSail (try_step 0 false) s` (hart stays active) + `Configured s` (all non-volatile registers equal
    `resetState`'s) + `Retired` (step succeeded and `minstret` += 1, i.e. no trap/illegal/fetch fault) + `Runs n`.
  - `Contract.lean`: `CodeAt`, `ImageLoaded`, `CalleeSaved`, `Implements entry frame spec`
    (RISC-V C ABI: args a0.., returns to ra with a0 = spec args, callee-saved + sp preserved,
    memory outside [sp-frame, sp) unchanged, `Configured` preserved, every step `Retired`).
  - `Config.lean`: a few `decide +kernel` facts about `resetState` (misa = I+M, privilege M, PMA list, MIE = 0).
  - `Allowed.lean`: `isIM : instruction → Bool` whitelist + theorem: every aligned code word of the image
    decodes (in `resetState`) to an `isIM` instruction. With RAM non-executable this covers every executed instruction.
  - `Spec*.lean`: the math (e.g. `combine x = 3x+1`, `polyEval a x = ∑ aᵢ xⁱ` in `ZMod (2^31-1)`).
  - `Theorems.lean`: final statements; imports `Slop` only to name the proof terms. Nothing else in human/ imports slop.

## slop/ (kernel-checked, not read)
1. Oracle interpreter `runOracle known knownMem : SailM α → Option α` (closed; unknown reads / writes → none) +
   soundness lemma vs `runSail`. Fetch/decode/interrupt-check of each *concrete* word are closed facts proved by
   `decide +kernel`. Decode's dependence on misa etc. is discharged by `Configured`. Never unfold the 4 MB decoder symbolically.
2. ~30 per-instruction-kind `execute` lemmas (symbolic rd/rs/imm/GPRs/mem) by unfold+simp; one shared
   `mem_access_ok` lemma for loads/stores (M-mode identity translation, PMA, empty PMP, alignment).
3. One `try_step` skeleton lemma: fetch = w ∧ decode w = i ∧ execute i = ok s' → step s = some (tick s') ∧ Retired.
4. Per-function proofs, parametric in own base address and callee addresses; code is *computed*
   (`combineCode b inc dbl` encodes the `jal` offsets); callee `Implements` used as hypotheses at `jal` sites.
   Link check: `combineCode 0x5c 0xc8 0xa4 = Image slice` by `decide`.
   Word lemmas are keyed by 32-bit value and shared across functions/programs.

## Known gaps vs real Airbender (state explicitly)
- Non-determinism: every Zicsr form on CSR 0x7c0 as Airbender's transpiler accepts it (source 0: read; rd = x0:
  no-op write; other combinations panic there and have no next state here). A read with no answers left is stuck
  (the theorems give enough).
- Delegations: only the Blake2s round function (CSR 0x7c7, as the VM/replayer runs a call: one macro step over the
  whole run of 7/10 `csrrw` words). Not modelled: 0x7c8 (Blake2s G function), 0x7ca (u256 bigint), 0x7cb-0x7ce
  (Keccak).
- Airbender halts when PC is unchanged (`j .`); we state `step s = some s`-style fixpoint at the halt address.
- Modularity with `+relax`: theorems are re-instantiated per layout; reused across relinks are the kind lemmas,
  word lemmas and proof scripts. Option B later: `-relax` + modelled relocations.
- Later: differential testing of Sail C emulator / Airbender `cli run` vs kernel evaluation; simulation proof
  `runSail` ≈ lean-sail's interpreter.

## Update 2026-10-12 (v0.0.8, second architecture review): symbolic execution by the kernel
- `kernel_rfl` (Eq.refl checked only by the kernel) evaluates the WHOLE official `try_step` with symbolic GPRs via the
  write-tracking oracle `Wr.oracleGo`, as long as nothing branches on symbolic data (`StepAddi.lean`: ~1 s).
  Per-instruction `execute` lemmas and a try_step decomposition are therefore unnecessary.
- Loads/stores with symbolic addresses (sp-relative, pointers): Sail branches on the address in pure functions
  (`is_aligned_vaddr`, `split_on_page_boundary` intra-page check, PMA `range_subset` (2x per store), `mag_pma_check`
  alignment; `jump_to` alignment for jalr). Plan:
  1. Oracle memory: `Known.code` (partial, image bytes, answers instruction fetch only) + `Known.data` (TOTAL,
     symbolic, = s.mem); memRead/memWrite of data use `readBytes`/`writeBytes` at the symbolic address, never deciding
     address equality in the kernel. Soundness: `s'.mem = K'.data`.
  2. Tactic `sym_step`: Kernel.whnf the oracle run until stuck on a Bool `c` about symbolic data; prove `c = true/false`
     from hypotheses (`simp only [is_aligned_vaddr, range_subset, ...]; bv_omega`), rewrite the (small) residual, continue;
     finish with kernel_rfl. Branches on data (bne, div) via `by_cases` beforehand.
  3. `step_of_sym`: package the StepAddi glue (Configured, frame via write log) so a function proof is one `sym_step` per
     static instruction. Loops: prove the body once with symbolic index, induct on the trip count.
- Contract hypotheses in bv_omega-friendly form: `sp.toNat % 16 = 0`, `RAM_START + frame ≤ sp.toNat ≤ RAM_END`, `ra % 4 = 0`.

## Speed plan (2026-10-12): everything in seconds, small modular steps
- User rule: minutes are a design bug; keep everything fast and small. Agent convention: a few seconds per file
  (~10 s soft target), hard kill 60 s / 4 GB.
- Suspected costs in sym_step: every separate kernel call re-runs Sail's reset (`resetState`) and the fetch/decode
  prefix (no cache across calls); `clean` walks huge residual terms in Meta.
- Baby steps, each measured on its own:
  1. Precompute the reset register values once as a definition (kernel-normalised), proved equal to `resetState.regs`
     in ONE kernel check; use it in all oracle runs. Measure `try_step_addi_vals` before/after.
  2. Measure each sym_step phase separately on `ret` (whnf, findStuck, clean, decide, rewrite).
  3. Modular layering: (a) per distinct instruction WORD, a lemma `step` = simple effect (setReg / writeBytes),
     parametric in PC and operands (one per word, ~1 s, cached by lake, reused across functions and layouts);
     (b) per function: compose word lemmas by plain rewriting + bv_omega (no Sail evaluation at all);
     (c) link: image bytes at addresses = words (decide).

## Update 2026-10-12 (v0.0.9-v0.0.10): own RV32IM spec, symbolic execution by simp
- Sail symbolic execution was too slow (minutes per `ret`). Program proofs now run against `human/Human/RV32.lean`
  (~150 readable lines: decoder from the encoding tables, one line of behaviour per instruction kind, Airbender
  memory map, `none` = unprovable). Sail stays for a later per-instruction equivalence proof (`execute_ITYPE`, ...).
- Contract (`human/Human/Call.lean`): `Implements code frame post` (any placement) and `ImplementsAt entry code
  callees frame post` (fixed address, callees' code assumed at theirs); `Returns` = back at ra, callee-saved
  registers restored, memory changed only in `[sp - frame, sp)`.
- Proofs (`slop/Slop/RV/`): goal-directed symbolic execution `∃ m s', run m S = some s' ∧ P s'`, one `simp` per
  instruction (fetch facts from `CodeAt`, generated `decode` lemma per word, per-kind `exec` lemmas, byte-memory
  lemmas, side conditions by `bv_omega`); calls use the callee's `Implements` theorem (`run_call`), so each function
  is proven once. inc 4.6 s, double 4.7 s, combine 11 s (two calls).
- Modularity: a function's proof depends on its own words and its callees' contracts only. Relinking that moves a
  callee changes the caller's `jal` words, so the caller's proof (seconds) reruns; the callee's does not.

## Rule of thumb (2026-10-13): constant cost per use
Whenever a proof touches large data or many cases (big symbolic states, long tables, many instructions), avoid
steps whose cost grows with that size: unfolding definitions, "by computation" checks (`rfl`, `decide`, kernel
evaluation) on big terms, and re-deriving the same fact at every step. Prove small general lemmas once (about a
tiny variable state, one table entry, one instruction) and use them as ordinary rewrites; each use then costs the
same no matter how big the surrounding data is. Example: "a jump does not change register reads" proved once on a
variable state and cited by name, instead of being re-checked by unfolding the whole symbolic state at every use
(that unfolding made simp hang and the kernel run out of stack).
