# verifier_evm heuristics

Terse pointers for optimizing the hand-written EVM/Yul GKR verifier (`gkr.sol` +
generated `circuit.yul`). Regenerate gas numbers with `bash stats.sh`; superseded
variants live in `private/gkr_with_old_variants.sol`.

## Compiler / toolchain
- solx crashes & clobbers memory often — solc is the reliable baseline.
- solx/LLVM has no "stack too deep" (compiles what solc can't), but its spills corrupt scratch on bad layout.
- Plain `assembly { }` = **no spill** (memory-unsafe); `assembly ("memory-safe")` re-enables stack→memory spilling.
- Always `--force` when benchmarking (else artifacts are reused and solc/solx look fake-identical).
- `no_rematerializer` profile (`foundry.toml`): -5.7k init gas on solc, +6/round.
- Memory-unsafe assembly kills spilling contract-wide → keep the bench/gen harness in a *separate* contract.

## Memory safety (intentionally unsafe)
- Never rely on the free-mem pointer `0x40` — hand-place every region.
- Regions must not overlap live data; put spill-sensitive slots *above* where the compiler spills.
- `mstore` spill-risk values to a reserved slot yourself; a bare `let` can come back garbage under pressure.

## Stack & inlining
- Every `let x := …` hints "push x to stack" → inline complex exprs for compiler scheduling freedom. **Highest-leverage habit.**
- Avoid function calls in hot paths (stack/register pressure); keep a function only if genuinely reused.
- But in an already-tight routine, more inlining can plateau/regress — re-bench.
- Operand/draw order changes codegen: dual sumcheck draws `r` **before** the claim check (≤6/round on solc); plain non-packed is the opposite.

## Field arithmetic
- We compute **non-canonically**: draws are `r ∈ [0, 2^128)`, can exceed `P = 2^128 - 159`. Safe only if every consumer funnels through `mulmod` before adding to a reduced value.
- eq values are always multiplicands → store **unreduced** (≤~5P); never addmod-chain raw eq.
- `mod(add(…))` beats `addmod(…)`.
- Use `P`/`MASK` constants directly (local copies = no gain); Yul rejects some const-exprs → recompute as products.

## Calldata / memory I/O
- u128 unpack (BE, high lane first): `x0 := shr(128, word)`, `x1 := and(word, MASK)`.
- Integers BE fixed-width (`to_be_bytes`); hashes/caps/roots raw 32B. Keep Rust emit ↔ EVM decode in lockstep.
- `calldatacopy` for bulk init blocks (952 vs 5911 gas); `calldataload` only when the words are already on stack.

## Misc
- Hand-scheduled Yul ≈4× cheaper than high-level Solidity on the hot loop.
- `sumcheck_compress_1pass`: -8% compress_gas on solx vs 2pass (revisit if solx-optimizing).
- LF line endings.

## For AI agents (Claude/Codex)
Process notes; human devs can skip.
- Validate on solc first; treat solx as a second target to tune after.
- Get it correct under no-spill (`assembly {}`) first, *then* try `("memory-safe")` spill for a boost — and re-verify nothing got clobbered.
- Explore variant matrices in a `/tmp` copy; keep committed `gkr.sol` lean (active path + each family's winner).
- Keep a family's **winning** variant even after it's inlined out of the live path (e.g. now-unused `sumcheck_round_dual`) — ready to un-inline later to trade gas for bytecode. Prune only losers; archive in `private/gkr_with_old_variants.sol`.
- Re-run `stats.sh` after each change.

### Design notes & TODO (folded from old STRATEGIES.md)
- **Init:** 128 evals = 8 polys×16 (2048B); poly0/1 = perm read/write product, poly2–7 = 3 logup (num,den) pairs. Flow (Rust ref; our `gkr_init_inlinefold` folds inline): absorb evals → draw `r0..r3`+`alpha` → eq[16] → `claim_i = dot(poly_i, eq)` → batch w/ `alpha` → check logup accs (`num==0 && den!=0`); read/write products passed on, not checked here.
- **TODO — two transcript layers (unbuilt):**
    - global-statement: absorb final regs/PC/ts + unified memory cap → global mem/perm challenges (single unified chunk → derive directly).
    - chunk-proof: absorb global challenges + setup/memory/witness caps → local logup challenges (`lookup_alpha`, additive), then GKR+WHIR.
- **Open Qs:** read/write product handling (return vs check); revert-on-logup-fail in init (likely yes); store `r0..r3` vs only `eq[16]`; reproduce Rust eq-prefactor use (first 3 challenges in the dim-reducing sumcheck, 4th for the final check); are canonical draws needed for soundness (skipped now).
