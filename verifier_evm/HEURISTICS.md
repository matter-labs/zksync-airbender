# verifier_evm heuristics

Hard-won lessons from hand-writing and benchmarking the EVM/Yul GKR verifier
(`gkr.sol` + generated `circuit.yul`). These are durable rules of thumb; raw gas
tables and the full variant matrix live in `private/BENCHMARKS.md`.

## Compiler / toolchain (solc + solx)

- **Develop and validate on solc first.** solx clobbers memory and crashes far
  more often. Treat solx as a second target you tune for, not the baseline.
- **Always benchmark both compilers with `--force`.** Without it Foundry reuses
  artifacts and solc/solx numbers look falsely identical. Canonical command:
  ```sh
  forge test -vv --force && forge test -vv --force --use $(which solx)
  ```
- **No-spill vs spill.** Plain `assembly { }` (memory-*unsafe*) **disables** the
  compiler's stack→memory spilling; `assembly ("memory-safe")` **re-enables** it.
  Get the code correct under no-spill first — no spills means the compiler can't
  stomp your hand-placed memory regions. Only enable spill to relieve a genuine
  "stack too deep", or to chase a gas boost, and then re-verify nothing got
  clobbered.
- **`no_rematerializer` optimizer profile.** Dropping the `m` (Rematerialiser)
  step from the optimizer sequence saves ~5.7k init gas on solc — it stops the
  recomputation of subexpressions (e.g. `p12`/`p34`) at each use site under stack
  pressure — at a cost of ~+6 gas/sumcheck-round. See `foundry.toml`.
- **Keep the generator/bench harness in a separate contract** from the verifier.
  Memory-unsafe assembly disables spilling for the *entire* enclosing contract,
  so isolating the generator means it never competes with the verifier for stack
  budget (matters under solx no-spill / solc `no_rematerializer`).

## Memory-safety discipline ("corrupt safely")

The verifier is intentionally memory-unsafe: it hand-places every region (seed,
eq table, point array, gas-stash slots) at fixed byte offsets and never uses
Solidity's allocator. This is safe **only** while these invariants hold:

- **Never rely on the free-memory pointer (`0x40`).** Manage all scratch by hand.
- **Hand-placed regions must not overlap live data**, and spill-sensitive slots
  must sit **above** where the compiler spills. Example: `GKR_INIT_GAS_PTR = 4256`
  is the lowest offset where solx stopped clobbering it across the
  `gkr_init_inlinefold` path; the eq table was likewise moved up out of the
  transcript scratch region so spills can't stomp it.
- **When stack pressure would spill a value, stash it explicitly** to a reserved
  slot with `mstore` — don't trust a bare `let`. Observed: `let init_gas := gas()`
  came back as garbage until it was stashed to a reserved slot.

## Stack pressure / functions

- **Prefer inlining over Yul helper calls in hot/tight paths.** Function calls
  add stack pressure and trigger stack-too-deep; keep something as a function
  only when it is genuinely reused.
- Note the limit: micro-inlining *inside* an already-tight routine does **not**
  reliably cut gas — aggressive inlining / removing `let` bindings gave no
  improvement on the packed dual sumcheck.

## Field arithmetic / encoding

- **Non-canonical draws are fine.** Drawing `r := and(seed, MASK)` (or
  `shr(128, seed)`) gives `r ∈ [0, 2^128)`, which can exceed `P = 2^128 − 159`.
  Safe as long as every consumer funnels `r` through `mulmod` before adding it
  into a reduced accumulator. `mod(seed, P)` costs ~2 gas/round more. Canonical
  drawing is intentionally skipped in the prototype.
- **eq values are always multiplicands**, consumed via `dot_eq`/`mul_assign`. So
  they may be stored **unreduced** (up to ~5P) with no reducing `mod` on stores.
  Never addmod-chain raw eq values; if a future consumer needs `< P`, reduce on
  load or switch to a reducing eq builder.
- **`mod(add(...))` beats `addmod(...)`** in the Horner path.
- **Use the `constant`s `P` and `MASK` directly inside assembly.** Local copies
  (`let p := P`) give no gas benefit and add copy-paste risk. Yul also rejects
  some const-expressions (e.g. `GKR_INIT_FIELD_ELEMENTS`) inside assembly —
  recompute them as a product of accepted constants.

## Calldata / memory I/O

- **`calldatacopy` for bulk blocks** you'll re-read from memory. The 2048-byte
  init block costs ~952 gas via `calldatacopy` vs 5911+ for load/store loops.
- **`calldataload` when the words are also needed on the stack immediately** for
  arithmetic. The sumcheck round already needs `w0,w1` on stack, so loading is
  cheaper than copying there.
- **Byte convention** (keep Rust emit and EVM decode in lockstep):
  - Integers: fixed-width big-endian (`u32`/`u64`/`u128 ::to_be_bytes`).
  - Hashes, Merkle caps, roots: raw 32 bytes.
  - Packed `u128` pair is `[x0:16][x1:16]` → `x0 := shr(128, word)`,
    `x1 := and(word, MASK)`. Smaller lanes follow the same high-to-low rule.

## Structure / method

- **Hand-scheduled Yul beats high-level Solidity ~4×** on the hot loop
  (~360 vs ~1300–1550 gas/round). Manual scheduling is still required.
- **Explore variant matrices in a `/tmp` copy** of `verifier_evm/`; keep the
  committed `gkr.sol` to the single active variant only.
- **`sumcheck_compress_1pass` is −8% compress_gas on solx vs 2pass** and passes
  all six `stats.sh` configs — a candidate worth revisiting if optimizing for
  solx (it lost to 2pass on the solc-first baseline).
