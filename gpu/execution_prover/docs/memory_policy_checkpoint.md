# Memory-policy checkpoint — 2026-09-08

Work is parked on `rr/v3_memory_policies` at the user's request. GPU measurement
controllers and the completion watcher are stopped. Circuit geometry, generated
circuit code and verifiers are unchanged; bigint's trace-length reduction is a
separate PR.

The implementation includes the 90 valid setup/memory/witness policies, fused
and in-place NTT paths, deferred separate oracle openings, shorter WHIR/input
allocation lifetimes, exact arenas, offline sweep/generation and production
preset replay. The generated production table is **empty**. Explicit-budget
production admission therefore rejects requests until measured presets are
installed; unbudgeted production retains its default policy.

## Measurement state

The timed sweep completed **48 GiB for all 12 circuits**: 90 policies per
circuit, two warmups and five timed proofs per fitting policy. The 46 GiB bigint
job was interrupted. No lower budget is certified for all circuits. A separate
fit-only smoke found 54/90 bigint policies fit at 38 GiB and none fit at 36 GiB.
The full campaign was intended to cover 16–48 GiB in 2 GiB steps and refine
boundaries/policy changes at 0.5 GiB. Every emitted budget must fit all circuits.

The maximum-input diagnostics below used a 48 GiB arena on an RTX PRO 6000
Blackwell Server Edition (188 SMs, 128 MiB L2). Input sizes include production
allocator rounding. Peaks include the target and the largest follower's input
bundle: standalone I&T, 3,222,275,072 bytes. CUDA context/driver/NTT-table overhead
is outside the arena. These are synthetic maximum-capacity allocation probes;
CPU proof parity is a separate verification gate.

| Circuit | Total input MiB | Minimum peak GiB | Maximum peak GiB |
| --- | ---: | ---: | ---: |
| Bigint | 1,176.001 | 37.20 | 42.23 |
| Blake2 G | 792.001 | 15.45 | 17.23 |
| Blake2 compression | 650.001 | 23.92 | 28.96 |
| Keccak | 1,128.001 | 25.48 | 30.94 |
| Inits/teardowns | 3,073.001 | 18.08 | 20.53 |
| Load/store subword | 1,460.001 | 25.31 | 27.44 |
| Load/store word | 1,460.001 | 22.19 | 23.57 |
| Add/sub/LUI/AUIPC/MOP | 1,396.001 | 22.74 | 25.49 |
| Jump/branch/SLT | 1,524.001 | 25.49 | 29.12 |
| Mul/div unsigned | 1,460.001 | 31.87 | 34.87 |
| Shift/binary | 1,524.001 | 27.81 | 31.31 |
| Unified | 996.064 | 20.74 | 24.87 |

## Verification and remaining work

All 13 final policy/ownership GPU fixtures passed: queued CPU-proof parity for
full, retained-monomial and in-place openings across add/sub, unified and
setup-less I&T; all witness transitions; and queued unified memory-commitment
parity. They assert device input reservations are released before job finish.
The two exact-budget GPU tests also passed. The latest replay CLI review passed
17 execution-prover CPU tests, and the coordinator passed 32 Python tests.
Single/multiple-source callback ownership regressions failed before the Rust
2021 capture fix and passed after it.

Earlier NTT gates passed seven expanded in-place tests, 24 existing default NTT
tests and four matching evaluation-leaf fixtures. Earlier default proof timing
found no measurable regression on add/sub, unified and Blake compression; the
latest comparison after input retirement stopped at **14/36 processes**, so its
planned six pairs per circuit are incomplete and do not establish a final
regression result. Generated preset replay has passed CPU checks only; no GPU
preset replay is claimed while the table is empty.

Finish the timing and exact-budget campaign, review the winners, then rebuild
with candidate presets and replay every selected circuit/budget through normal
production admission and selection. Compare proof fingerprints, fit and timing
before treating the preset table as ready. See [memory_policies.md](memory_policies.md)
for sweep and replay usage.

## Local artifacts and resumption

Raw measurements and frozen binaries remain under the ignored
`target/memory-policy/` directory in the original worktree. They are not stored
in this branch. The completed timed 48 GiB results were revalidated and exported
to `v3-budget-sweep/results/{state.json,summary.json,diagnostics.csv,accepted.csv}`.
The interrupted 46 GiB CSV/log remain under `results/runs/46/`; they are partial
and will be rerun on resume. Final GPU logs/results are `task6-final-*.log` and
`task6-final-policy-results.json`; partial default timing is in
`timing-task6-default/`; full-input peak diagnostics are in
`v3-peaks48-full-inputs/`.

The frozen sweep binary is `v3-budget-sweep/gpu_memory_sweep`, SHA256
`82538202f74e706527ac74d4e9e46f9931ef82f3139493e615341eb6bf3390a2`.
It predates the replay-only CLI additions and must remain unchanged for resume
identity. To resume only when requested:

```sh
python3 gpu/execution_prover/scripts/memory_sweep.py \
  --binary target/memory-policy/v3-budget-sweep/gpu_memory_sweep \
  --output-dir target/memory-policy/v3-budget-sweep/results \
  --emit-rust target/memory-policy/v3-budget-sweep/measured.rs \
  --run-timeout-seconds 900 --resume
```

The coordinator revalidates completed CSVs and their hashes, reuses complete
48 GiB measurements, reruns interrupted jobs and releases the shared GPU lock
between circuits. Do not restart the old completion watcher while this work is
parked. The default timing script has no automatic resume mode; preserve its
existing samples when completing the missing comparison fixtures.
