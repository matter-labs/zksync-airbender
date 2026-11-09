# ci/ — the Lean CI job and its local reproduction

`.github/workflows/lean-formal-verification.yml` runs `verify.sh` (build, regressions, axiom audits, the 30 s module
budget, review check) on pull requests and pushes to `main` that touch `cs_formal_verification/` or the circuit
JSONs the spec imports (`cs/compiled_circuits/*_layout_no_caches_gkr.json`), and on manual dispatch. It is a
separate workflow: the `Rust CI` jobs and the `pr-checks` gate are unchanged.

Every step is a subcommand of [lean-ci.sh](lean-ci.sh); the workflow and the Docker reproduction call the same
commands.

| step | what | cached |
|---|---|---|
| `deps` | apt: git, curl, python3 (3.12; `module_budget.py` needs 3.11+), procps (`ps`, the budget sampler), zstd | no |
| `elan` | elan (pinned release) + the toolchain in `lean/lean-toolchain` | `~/.elan`, key = toolchain |
| `sail-gen` | `sail/regen.sh --bootstrap-sail` (builds the pinned Sail compiler with opam, generates the model), then requires the committed `sail-rv32/` files to be reproduced byte for byte | `sail-rv32/SailRV32{,.lean}`, key = hash of every `regen.sh` input (`lean-ci.sh sail-key`); on a hit nothing is generated |
| `lean-sail` | `sail/fetch-lean-sail.sh` (no upstream licence: fetched, never stored) | no |
| `mathlib` | `lake exe cache get` (clones the dependencies, downloads Mathlib's `.olean` files) | no (see below) |
| `verify` | `./verify.sh`, each of its steps timed | `.lake/build`, `.lake/module-cpu.tsv` (the budget ledger), `sail-rv32/.lake`, Clean's `.lake`; key = arch + toolchain + manifest + commit, restored from the newest entry with the same prefix |

The build cache is Lake's own build directory, not Lake's shared artifact cache (`LAKE_ARTIFACT_CACHE`, used on the
development machine): that cache is content-addressed and only grows, so each saved entry would carry every older
build. The plain build directory holds one build; Lake rebuilds exactly what changed (its traces are hashes, so the
fresh checkout's file times do not matter). The budget ledger is keyed by each module's Lake input hash, so an entry
saved by an older commit is used exactly as long as the module is not rebuilt; without it the budget check compiles
every module a second time.

## Threads and memory

There is no `lake build -j`: `LEAN_NUM_THREADS` sets both the threads of each Lean process and how many modules Lake
compiles at once, and peak memory grows with it. The workflow takes it from the dispatch input, else the repository
variable `LEAN_CI_THREADS`, else the default in the workflow. Lean does not read the container's CPU quota (`nproc`
reports the host's CPUs), so set it explicitly.

## Local reproduction ([sim.sh](sim.sh))

`ci/sim.sh image` builds `fvci:local` ([Dockerfile](Dockerfile): ubuntu:24.04, native arch, the apt packages of the
steps baked in). `ci/sim.sh run <store> <cpus> <mem> <threads> <rev> <from> <to> [log]` runs
[sim-job.sh](sim-job.sh), the workflow's steps in order, on `git archive <rev>` with `docker run --cpus --memory`
(no swap). `actions/cache` is simulated by zstd tarballs in the named volume `<store>`: a new store name is a cold
cache; `<from>`/`<to>` name the build cache entry restored and saved. `FVCI_STOP=sail` stops after the Sail model.
Each step prints `STEP <name> wall= cpu= peak=` (CPU and memory from the container's cgroup); `lean-ci.sh report`
prints the modules compiled, the slowest ones and the container's peak memory.
