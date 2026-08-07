# gpu_gkr_uniskip_bench

Standalone CUDA benchmark for one **uniskip** sumcheck pass. It is off the
`gpu/` crate DAG: nothing depends on it, and it depends on no prover crate, so
kernel shapes can be iterated on without building the prover stack.

## What it measures

A uniskip round with the skip factor **k fixed at 4**:

- 16 taps of a logical row live on the multiplicative subgroup `H` of size 16;
  the pass also evaluates the 16 cells of the odd coset `gamma*H`, giving
  `UNISKIP_CELLS = 32` cells per logical row.
- Plane-order layout: tap `t` of logical row `r` sits at element offset
  `r + (t << log_rows)` inside its column, with `log_rows = log_trace - 4`.
- The constants are shaped so k=3/5 would be a one-line change, but nothing is
  parameterized on k today.

Instead of consuming a real GKR layout, the bench runs a **deterministic
synthetic program** whose census (sources, term classes, groups, coefficient
applications) is pinned to production-shaped defaults and overridable from the
CLI. The eq tables and challenge point are synthetic too — not transcript-real.

## Build and run

```bash
cargo build --release -p gpu_gkr_uniskip_bench
.agents/bin/with_gpu_lock.sh target/release/gpu_gkr_uniskip_bench --log-trace 20
target/release/gpu_gkr_uniskip_bench --help
```

Any run that touches the GPU must go through `.agents/bin/with_gpu_lock.sh`;
building and `--help` do not.

## Status

Scaffold. The CLI parses and prints its configuration; the domain math,
synthetic program generator, and kernels land in follow-up work.
