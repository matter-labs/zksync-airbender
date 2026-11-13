# ci/ — the Lean CI job and its local reproduction

`.github/workflows/lean-formal-verification.yml` runs `verify.sh` (build, regressions, axiom audits, the module
budget, review check) when `cs_formal_verification/` or a circuit JSON the spec imports or the tests read
(`cs/compiled_circuits/*_gkr.json`) changes, nightly, and on manual dispatch. It is a separate workflow: the
`Rust CI` jobs and the `pr-checks` gate are unchanged. What each mode re-checks:
[TRUST_AND_REVIEW](../docs/TRUST_AND_REVIEW.md#what-ci-re-checks).

- **incremental** (pull requests, manual runs): restores the newest build of the same toolchain and dependencies,
  rebuilds what changed, reads the axiom audits from Lake's build log (`VERIFY_AUDITS=replay`), skips the review
  check's Lean inventory when its inputs are unchanged;
- **cold** (pushes to `main`, `stable`, `dev`, `av_gkr_compiler`; nightly; dispatch with `cold`): no build cache,
  fresh audits. Its build is saved and seeds the pull requests. The toolchain, the dependency checkouts, Mathlib's
  files and the Sail model are restored in both modes (regenerating the Sail model nightly would add ~10 min);
- **kernel replay** (job `kernel_replay`: nightly, or dispatch with `kernel_replay`): builds,
  then the kernel re-checks every constant (`lean-ci.sh kernel-check`, `KERNEL_CHECKER=paranoid`: `lake check
  --paranoid` on the lakefile's default targets, then `leanchecker` on the two Clean-importing modules). It runs on the
  runner host, not in a container, so that `lake check`'s `bwrap` sandbox gets user and mount namespaces; `lean-ci.sh
  kernel-probe` checks that first, and where `bwrap` cannot sandbox the job replays with `leanchecker` and fails.
  `backup-check.sh` runs the same job by hand. Host prerequisites: passwordless `sudo` that allows the
  `DEBIAN_FRONTEND=noninteractive` assignment (for `apt-get`), or git, curl, python3, procps, zstd, xz-utils and
  bubblewrap preinstalled; user namespaces for unprivileged processes (Ubuntu 24.04's AppArmor restriction off, or a
  bwrap profile allowing them).

The setup steps shared by both jobs are the composite action `.github/actions/lean-fv-setup`.

Every step is a subcommand of [lean-ci.sh](lean-ci.sh); the workflow and the Docker reproduction call the same
commands.

| step | what | cached |
|---|---|---|
| `deps` | apt: git, curl, python3 (3.12; `module_budget.py` needs 3.11+), procps (`ps`, the budget sampler), zstd | no |
| `elan` | elan (pinned release) + the toolchain in `lean/lean-toolchain` | `~/.elan`, key = toolchain |
| `sail-gen` | `sail/regen.sh --bootstrap-sail` (builds the pinned Sail compiler with opam, generates the model), then requires the committed `sail-rv32/` files to be reproduced byte for byte | `sail-rv32/SailRV32{,.lean}`, key = hash of every `regen.sh` input (`lean-ci.sh sail-key`); on a hit nothing is generated |
| `lean-sail` | `sail/fetch-lean-sail.sh` (no upstream licence: fetched, never stored) | no |
| `mathlib` | `lake exe cache get` for the modules the build imports (`dep_targets.py --cache-args`: 3082 of Mathlib's 8908 files; the cache tool adds their imports) | the dependency checkouts `.lake/packages` without build outputs (0.6 GB; Mathlib's git history most of it), the downloaded files and the cache tool binary `~/.cache/mathlib` (0.22 GB), key = manifest |
| `lean-deps` | the dependencies of the build apart from our code ([dep_targets.py](dep_targets.py)): the Sail model library, the Clean modules we import, the C objects of the test executable's dependencies | in the build cache |
| `kernel-check` | job `kernel_replay`: every constant of our modules replayed in the kernel, `KERNEL_CHECK_THREADS` (2) modules at a time | no |
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
The kernel replay (`leanchecker`) holds a whole imported environment per module it replays: 1.3 GB at 1 at a
time, 5.8 GB at 2 on 89 modules and 10.1 GB on all of them, over 15 GB at 4, hence `KERNEL_CHECK_THREADS` = 2.

**Recommendation:** 8 CPUs / 16 GB with `LEAN_NUM_THREADS` = 8 fits with margin (8 CPUs and 8 threads cut a cold build of our
code from 729 s to 379 s and a pull request's from 187 s to 106 s). On 4 CPUs use 4 threads; pull requests then take
~7 min instead of ~5.5. More than 8 threads gains little (a pull request keeps ~4-5 modules busy on average: the
import chain after an artifact change is the critical path). The arm64 container on an M3 Max is not the x86
runner: its first run is the real measurement, and the budget gate calibrates itself to it.

Cache sizes (zstd): toolchain 0.77 GB, dependency checkouts 0.6 GB, Mathlib files 0.22 GB, Sail model 0.6 MB,
build 0.41 GB per commit key. They share the repository's cache quota (10 GB by default) with the Rust jobs' caches;
old build keys are evicted first.

## Local reproduction ([sim.sh](sim.sh))

`ci/sim.sh image` builds `fvci:local` ([Dockerfile](Dockerfile): ubuntu:24.04, native arch, the `deps` step's packages
baked in). `ci/sim.sh run <store> <cpus> <mem> <threads> <rev> <from> <to> [log]` runs
[sim-job.sh](sim-job.sh), the workflow's steps in order, on `git archive <rev>` with `docker run --cpus --memory`
(no swap). `actions/cache` is simulated by zstd tarballs in the named volume `<store>`: a new store name is a cold
cache; `<from>`/`<to>` name the build cache entry restored and saved. `FVCI_STOP=sail` stops after the Sail model.
Each step prints `STEP <name> wall= cpu= peak=` (CPU and memory from the container's cgroup); `lean-ci.sh report`
prints the modules compiled, the slowest ones and the container's peak memory.

## Measurements (2026-11-09)

(Since 2026-11-10 `verify.sh` builds spec, proofs and tests in one `lake build` (step 2) and step 3 only runs the test
executable and the audits; the step 2 / step 3 split below is the earlier layout.)

Docker on an Apple M3 Max (linux/arm64, `ci/sim.sh`, the workflow's steps; `--cpus`/`--memory 15g`, no swap; never
OOM-killed). The self-hosted runners are probably x86_64: expect roughly 1.25x these times per core (an estimate,
not measured). "PR" = a realistic pull request on top of a warm cache of the previous commit: three circuit JSONs
and the Chi5 setup table re-serialised (same parsed JSON, pins updated) plus a proof edit; Lake rebuilds 295 spec/
proof modules and 61 test modules. Times are wall clock; CPU and memory per step are in the logs.

**Headline**

| run | 8 CPUs, 8 threads | 4 CPUs, 4 threads |
|---|---|---|
| warm no-op (incremental) | **55 s** | 58 s |
| PR (incremental) | **260 s** | 363 s |
| cold, our code (verify.sh, nothing cached) | **576 s** | 1026 s |
| cold CI run (setup from caches + our code) | ~17 min | ~26 min |
| zero caches, setup only | | **25.5 min** |
| zero caches, total | | **42.6 min** (setup 60%, our code 40%) |
| kernel replay job (`leanchecker`, 2 at a time) | | 24.8 min, 10.1 GB |

Warm runs, step by step (8 CPUs): restores ~15 s, Mathlib files 12 s, dependencies 10 s, `verify.sh` 18 s (build
2 s, regressions and replayed audits 7 s, budget 6 s, review 3 s). PR (8 CPUs): `verify.sh` 223 s = build 105 s,
regressions/audits 48 s, budget 6 s, review 64 s (its inputs changed). Thread sweep for the PR on 8 CPUs: 4 / 6 / 8
threads = 310 / 280 / 235 s for `verify.sh`, peak 1.4 / 1.9 / 2.4 GB.

**Worst case: zero caches** (4 CPUs, 15 GB, 4 threads; empty volumes, nothing seeded)

| part | step | wall | CPU | peak memory | disk after |
|---|---|---|---|---|---|
| setup | apt packages | 40 s | | | |
| setup | elan + toolchain download | 139 s | 14 s | 0.0 GB | +3.0 GB |
| setup | Sail packages (apt) | 31 s | 9 s | 0.1 GB | +1.1 GB |
| setup | Sail model: opam bootstrap + `regen.sh` | 592 s | 1189 s | 1.4 GB | +1.9 GB |
| setup | lean-sail | 0 s | 0 s | | |
| setup | Mathlib (`cache get`, all 8908 files then) | 233 s | 160 s | 0.3 GB | +8.3 GB |
| setup | dependencies: Sail model library, Clean, 1736 dependency objects | 497 s | 1152 s | 3.3 GB | +0.4 GB |
| **setup total** | | **1533 s (25.5 min)** | 2525 s | | 16.4 GB |
| our code | build (verify.sh step 2) | 729 s | | 4.7 GB | |
| our code | tests, test executable, fresh audits (step 3) | 217 s | | | |
| our code | module budget (step 4) | 20 s | | | |
| our code | review check (step 5) | 61 s | | | |
| **our code total** | | **1026 s (17.1 min)** | 3722 s | 4.7 GB | +2.4 GB |
| **total** | | **2559 s (42.6 min)**: setup 60%, our code 40% | 6247 s | | ~19 GB with the cache archives |

The setup and our code are split by building the dependencies first (`lean-deps`, a separate `lake build` of the
targets `dep_targets.py` lists), so `verify.sh`'s build compiles only our modules. The toolchain and Mathlib
downloads are network-bound (GitHub's release downloads answered 504 for minutes at a time during these runs; both
steps retry). With the CI caches, a cold run's setup is ~1 min of restores plus the dependencies (387 s on 8 CPUs,
dominated by the Sail model library's sequential chain).

**If Mathlib's cache server were unavailable** (estimate, not measured): Lake would compile the 1521 Mathlib
modules our build imports plus ~220 of Batteries, Aesop and Qq. A sample of 48 of those modules took 2.5 s CPU each on
the M3 Max (3.0 s over all of Mathlib), so ~72 min of CPU: about 20-25 min on 4 cores and 12-15 min on 8, more on an
x86 runner.

Native reference (M3 Max, artifact cache off, before the warm-run changes above): PR 555 / 465 / 435 s at 4 / 8 / 12
threads, no-op 100 s.
