# Memory requirements after PR #434 — 2026-09-11

`rr/v3_memory_policies` was rebased onto PR #434 at
`4c8f0b7397a6c7ba7467f9431957aabaf1cdda02`. The PR stack halves bigint's
trace domain from 2^22 to 2^21, mul/div's from 2^24 to 2^23, and standalone
I&T's set count from 16 to 8. Standalone I&T still has 2^24 rows per set.

The rebase had no conflicts. Two bigint parity/profiling fixture arguments
still hard-coded the previous domain; they now use `CircuitType` geometry.
Production memory-policy code required no adjustment. The sweep's factory
already derives maximum trace length and I&T capacity from the compiled
circuit, including window IDs and local page indices.

## Input sizes and allocation peaks

All **12 circuits × 90 policies** completed successfully in a 48 GiB arena.
These are fit-only synthetic maximum-capacity probes: one proof per policy,
with matching proof fingerprints across policies for each circuit. They are
not a timing campaign or a valid VM-execution corpus.

Input size includes the circuit's trace, I&T where present, decoder, setup
evaluations and cached setup trees, caps, challenges and allocator rounding.
Peak includes the target plus the largest follower's complete input bundle.
That follower remains standalone I&T, now **1,611,662,336 bytes**
(**1,537.001 MiB**), 1.5 GiB smaller than before. Driver/context allocations and
NTT tables outside the device arena are excluded.

| Circuit | Input MiB | Minimum peak GiB | Maximum peak GiB |
| --- | ---: | ---: | ---: |
| Bigint | 588.001 | 18.62 | 21.13 |
| Blake2 G | 792.001 | 13.95 | 15.73 |
| Blake2 compression | 650.001 | 22.42 | 27.46 |
| Keccak | 1,128.001 | 23.98 | 29.44 |
| Inits/teardowns | 1,537.001 | 9.08 | 11.53 |
| Load/store subword | 1,460.001 | 23.81 | 25.94 |
| Load/store word | 1,460.001 | 20.69 | 22.07 |
| Add/sub/LUI/AUIPC/MOP | 1,396.001 | 21.24 | 23.99 |
| Jump/branch/SLT | 1,524.001 | 23.99 | 27.62 |
| Mul/div unsigned | 740.001 | 15.96 | 17.46 |
| Shift/binary | 1,524.001 | 26.31 | 29.81 |
| Unified | 996.064 | 19.24 | 23.37 |

The maximum of the per-circuit minimum peaks is **26.3115 GiB**, for
shift/binary. These observed peaks alone do not certify the same-sized exact
arena: placement and fragmentation must also fit.

## Exact arena checks

**All 12 circuits fit a 26.5 GiB exact arena**, using one minimum-peak policy
per circuit selected from the 48 GiB diagnostic rows. Each successful proof
matched its 48 GiB fingerprint, with the same largest-follower input overlap.
This is an all-circuit fit observation, not a fastest-policy preset.

At **26 GiB**, **none of the 90 shift/binary policies fit**. Every failure was
an arena allocation failure in the target-plus-largest-follower probe, and the
worker exited cleanly without a CUDA fault. Therefore 26 GiB fails the
all-circuit requirement. The observed boundary on the 0.5 GiB grid is 26.5 GiB;
no finer exact-arena boundary was measured.

The passing 26.5 GiB policy for circuits with witness columns uses full witness
commitment, drops its cosets after commitment, and fully rematerializes them
for openings; setup/memory openings also use deferred full materialization.
Standalone I&T uses in-place memory openings; its zero witness/setup widths
make those policy fields immaterial. This observation does not rank proof time.

Local evidence: `exact/{plan.json,results.json}` and per-circuit CSVs/metadata
under `exact/runs/26.5/`; the failing 90-policy search is under
`lower26/runs/26/unrolled_non_memory_shift_binary/`. All paths are relative to
`target/memory-policy/pr434-20260911/` in the measurement worktree.

## Validation and measurement identity

- `cargo check -p gpu_execution_prover --features memory_sweep --tests` and
  `cargo check -p gpu_circuit_prover --tests` passed.
- 20 execution/context CPU tests and 32 Python coordinator tests passed.
- Four release GPU tests passed: bigint and mul/div CPU-proof parity at their
  new domains, and in-place openings plus witness-policy reuse on eight-set I&T.
- Every memory probe checked production transfer-byte accounting, proof
  consistency, empty allocator reservations at completion and clean CUDA exit.
  GPU/process snapshots were taken under the shared lock, released per circuit.

The device was an RTX PRO 6000 Blackwell Server Edition, 188 SMs, 128 MiB L2,
driver 610.57.04, UUID `GPU-3f788795-e923-51f3-e679-b31e091dc3b1`. This is a
different physical device from the September 8 measurements. The comparisons
above concern allocation geometry; no causal proof-time comparison is claimed.
The configuration was Sec100 with coefficient leaves and the default allocator
(1 MiB blocks, 16-block small pool, 256-byte small chunks).

Frozen release sweep binary SHA256:
`cc7444fb04d69212b2a028af51e2546c5ecea0682713ae0de121314098b30a22`.
Local artifacts are under `target/memory-policy/pr434-20260911/`:
`source.json`, `peaks48/{state.json,memory-summary.json,diagnostics.csv}`, and
per-circuit CSVs/logs/device metadata under `peaks48/runs/48/`. The build/test
logs and frozen archives are in the same directory. These raw files are ignored
and are not stored in the branch.

The September 8 [checkpoint](memory_policy_checkpoint.md) is historical.
Its timed campaign remains stopped. Production preset generation and GPU
preset replay have not been resumed; the generated production table is empty.
The fit measurements here do not select the fastest policy or establish a
proof-time regression result.
