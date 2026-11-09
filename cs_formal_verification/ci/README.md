# ci/ — the Lean CI job and its local reproduction

`.github/workflows/lean-formal-verification.yml` runs `verify.sh` (build, regressions, axiom audits, the module
budget, review check) when `cs_formal_verification/` or a circuit JSON the spec imports or the tests read
(`cs/compiled_circuits/*_gkr.json`) changes, nightly, and on manual dispatch. It is a separate workflow: the
`Rust CI` jobs and the `pr-checks` gate are unchanged. Two modes (what each re-checks:
[TRUST_AND_REVIEW](../docs/TRUST_AND_REVIEW.md#what-ci-re-checks)):

- **incremental** (pull requests, manual runs): restores the newest build of the same toolchain and dependencies,
  rebuilds what changed, reads the axiom audits from Lake's build log (`VERIFY_AUDITS=replay`);
- **cold** (pushes to `main`, `stable`, `dev`, `av_gkr_compiler`; nightly; dispatch with `cold`): no build cache,
  fresh audits, then the kernel replays every constant of our modules (`leanchecker`). Its build is saved and seeds
  the pull requests. The toolchain, the dependency checkouts, Mathlib's archives and the Sail model are restored in
  both modes (regenerating the Sail model nightly would add ~10 min; not done).

Every step is a subcommand of [lean-ci.sh](lean-ci.sh); the workflow and the Docker reproduction call the same
commands.

| step | what | cached |
|---|---|---|
| `deps` | apt: git, curl, python3 (3.12; `module_budget.py` needs 3.11+), procps (`ps`, the budget sampler), zstd | no |
| `elan` | elan (pinned release) + the toolchain in `lean/lean-toolchain` | `~/.elan`, key = toolchain |
| `sail-gen` | `sail/regen.sh --bootstrap-sail` (builds the pinned Sail compiler with opam, generates the model), then requires the committed `sail-rv32/` files to be reproduced byte for byte | `sail-rv32/SailRV32{,.lean}`, key = hash of every `regen.sh` input (`lean-ci.sh sail-key`); on a hit nothing is generated |
| `lean-sail` | `sail/fetch-lean-sail.sh` (no upstream licence: fetched, never stored) | no |
| `mathlib` | `lake exe cache get` (clones the dependencies, unpacks Mathlib's `.olean` files) | the dependency checkouts `.lake/packages` without build outputs (0.6 GB; Mathlib's git history is 0.5 GB of it) and the downloaded archives `~/.cache/mathlib` (0.44 GB, ~8900 files fetched one by one otherwise), key = manifest |
| `lean-deps` | the dependencies of the build apart from our code ([dep_targets.py](dep_targets.py)): the Sail model library, the Clean modules we import, the C objects of the test executable's dependencies | in the build cache |
| `kernel-check` | cold mode: `leanchecker` replays every constant of our modules in the kernel, `KERNEL_CHECK_THREADS` (2) modules at a time | no |
| `verify` | `./verify.sh`, each of its steps timed | `.lake/build`, `.lake/module-cpu.tsv` (the budget ledger), `sail-rv32/.lake`, Clean's `.lake`, the dependencies' C objects (`airbender_tests` links every imported module; Mathlib's cache ships no objects: ~3100 clang compiles, ~6 min CPU, 40 MB); key = arch + toolchain + manifest + commit, restored from the newest entry with the same prefix |

The build cache is Lake's own build directory, not Lake's shared artifact cache (`LAKE_ARTIFACT_CACHE`, used on the
development machine): that cache is content-addressed and only grows, so each saved entry would carry every older
build. The plain build directory holds one build; Lake rebuilds exactly what changed (its traces are hashes, so the
fresh checkout's file times do not matter). The budget ledger is keyed by each module's Lake input hash, so an entry
saved by an older commit is used exactly as long as the module is not rebuilt; without it the budget check compiles
every module a second time.

## Threads, memory and runner

There is no `lake build -j`: `LEAN_NUM_THREADS` sets both the threads of each Lean process and how many modules Lake
compiles at once. The workflow takes it from the dispatch input, else the repository variable `LEAN_CI_THREADS`,
else 8. Lean does not read the container's CPU quota (`nproc` reports the host's CPUs), so it is set explicitly.

A Lean process maps the imported `.olean` files (Mathlib alone is 6.6 GB unpacked); under a container memory limit
they count as page cache, which the kernel reclaims. The process's own (anonymous) memory is what can run out. In
the container (15 GB limit, never OOM-killed): a cold build peaks at 4.7 GB anonymous with 4 threads and 5.3 GB
with 8; a pull-request build at 1.4 / 1.9 / 2.4 GB with 4 / 6 / 8 threads; page cache brought the total to ~10 GB.
`leanchecker` holds a whole imported environment per module it replays: 1.3 GB at 1 at a time, 5.8 GB at 2 on
89 modules and 10.1 GB on all of them, over 15 GB at 4, hence `KERNEL_CHECK_THREADS` = 2.

**Recommendation:** 8 CPUs / 16 GB with `LEAN_NUM_THREADS` = 8 fits with margin (8 CPUs and 8 threads cut a cold build of our
code from 729 s to 379 s and a pull request's from 187 s to 106 s). On 4 CPUs use 4 threads; pull requests then take
~7 min instead of ~5.5. More than 8 threads gains little (a pull request keeps ~4-5 modules busy on average: the
import chain after an artifact change is the critical path). The arm64 container on an M3 Max is not the x86
runner: its first run is the real measurement, and the budget gate calibrates itself to it.

Cache sizes (zstd): toolchain 0.77 GB, dependency checkouts 0.6 GB, Mathlib archives 0.44 GB, Sail model 0.6 MB,
build 0.41 GB per commit key. They share the repository's cache quota (10 GB by default) with the Rust jobs' caches;
old build keys are evicted first.

## Local reproduction ([sim.sh](sim.sh))

`ci/sim.sh image` builds `fvci:local` ([Dockerfile](Dockerfile): ubuntu:24.04, native arch, the apt packages of the
steps baked in). `ci/sim.sh run <store> <cpus> <mem> <threads> <rev> <from> <to> [log]` runs
[sim-job.sh](sim-job.sh), the workflow's steps in order, on `git archive <rev>` with `docker run --cpus --memory`
(no swap). `actions/cache` is simulated by zstd tarballs in the named volume `<store>`: a new store name is a cold
cache; `<from>`/`<to>` name the build cache entry restored and saved. `FVCI_STOP=sail` stops after the Sail model.
Each step prints `STEP <name> wall= cpu= peak=` (CPU and memory from the container's cgroup); `lean-ci.sh report`
prints the modules compiled, the slowest ones and the container's peak memory.

## Measurements (2026-11-09)

Native reference, Apple M-series (14 cores), `LAKE_ARTIFACT_CACHE` off as in CI, `verify.sh` on a warm build of the
previous commit. Scenario "PR": three circuit JSONs and the Chi5 setup table re-serialised (same parsed JSON, pins
updated) plus a proof edit; Lake rebuilds 295 spec/proof modules and 61 test modules. Peak memory is the summed
physical footprint of the `lean`/`lake` processes (page cache of the mapped `.olean` files excluded).

| scenario | `LEAN_NUM_THREADS` | build (step 2) | tests (step 3 build) | whole `verify.sh` | peak memory |
|---|---|---|---|---|---|
| warm no-op | 8 | 4 s | 4 s | 100 s | 0.9 GB |
| PR | 4 | 353 s | 111 s | ~555 s | 2.8 GB |
| PR | 8 | 289 s | 78 s | ~465 s | 3.5 GB |
| PR | 12 | 267 s | 72 s | ~435 s | 4.7 GB |

On a no-op, 80% of the time is the review check (`check_review.py`, ~50 s: it elaborates an inventory of every
claim module) and the three axiom audits (~37 s). Beyond 8 threads a PR build gains little: on average only ~5
modules compile at once (the import chain after an artifact change is the critical path).

Other steps: `lake exe cache get` 587 s with an empty `~/.cache/mathlib` (8908 files fetched one at a time on this
link), 74 s with it restored; the toolchain download 294 s; `sail/regen.sh --bootstrap-sail` 1380 s CPU (most of it
building OCaml and Sail with opam), none of these on a warm run.
