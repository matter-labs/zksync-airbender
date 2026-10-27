# Bounded compilation pool

The pool schedules ready, independent jobs under one aggregate resource guard.
It defaults to four workers and accepts one through four. The existing
`scripts/bounded_fv.py` remains the serial entrypoint, with its original behavior.
The additive guard delegates process measurement, the global lock and owned
descendant cleanup to that implementation; it changes only the explicit Lean
worker ceiling.

All members together remain limited to 2,560 MiB footprint, 5,120 MiB bounded
resident memory and 900 seconds. These limits are not multiplied by worker count.
Darwin uses libproc footprint/RSS. Linux footprint is anonymous memory plus
proportional shared memory, swap and huge pages; bounded resident excludes swap.
Mapped file pages are excluded from those Linux caps; total RSS is telemetry.
On Linux, the exact `lean --print-prefix` metadata query is excluded from the
compiler count. Its memory and elapsed time remain charged. Unknown arguments
and every other Lean invocation count as workers; Darwin retains its conservative
process-name count.
Replay selects a finite Lean thread stack on every host and records it in its
tool identity. Linux additionally sets a finite process stack limit; Darwin retains
and records its inherited process limit because the OS rejects changes.
Reservations guide admission; aggregate samples enforce these approximate budgets
and fail closed. They are not exact cgroup hard limits.

Admission leaves 128 MiB for the pool: reservations plus this overhead must fit
both aggregate caps. Missing peak estimates run exclusively with reservations
of 2,432/4,992 MiB. Explicitly exclusive jobs, or estimates above 1,216 MiB
physical or 2,496 MiB resident, also run alone. Estimates exactly at those half
boundaries permit two jobs. A reservation is not a guarantee about actual use.

## Normal verification

Run from `formal_verification/lean`, without another outer guard:

```sh
python3 scripts/check_lean.py --guard scripts/bounded_fv.py --workers 2 --output /tmp/airbender-verification-new
```

The output directory must be fresh. `--workers 1` selects serial probe admission;
the maximum is four. The current frontend pools cached, no-build freshness
queries. Dirty targets still go through the original guarded normal build, and
runtime/review leaves retain their serial guard. A successful no-build query
establishes freshness; its elapsed time is not proof elaboration time.

## Explicit job manifests

Each job has a safe unique label, argument vector, existing absolute working
directory, dependencies and a deadline of at most 900 seconds. Optional memory
estimates enable admission alongside other small jobs. For example:

```json
{
  "jobs": [
    {
      "label": "first",
      "argv": ["python3", "-c", "print('ready')"],
      "cwd": "/absolute/path/to/formal_verification/lean",
      "dependencies": [],
      "seconds": 10,
      "reserved_footprint_mib": 128,
      "reserved_resident_mib": 256,
      "exclusive": false
    }
  ],
  "inputs": {}
}
```

The optional `inputs` object maps absolute input paths to their exact SHA256
digests. The manifest and specified input bytes are checked before and after
execution. Add a job dependency for every required predecessor; parallel Lake
jobs must not race to produce the same prerequisite. The outer guard counts
actual Lean processes, including any additional compiler spawned by a member.

Use exactly one guard around the entire pool:

```sh
python3 -m scripts.compilation_pool.guard --lean-workers 2 --mib 2560 --resident-mib 5120 --seconds 900 --log /tmp/compile-pool.aggregate.log -- python3 -m scripts.compilation_pool.pool --manifest /tmp/compile-jobs.json --output /tmp/compile-pool-new --workers 2
```

Use absolute manifest/output paths and a fresh output directory. Pool members
must not acquire another guard or the shared global lock. The process controls
below likewise run without an enclosing guard. The guard emits one JSON receipt
with combined memory peaks, observed Lean worker peak and cleanup status; each
member has its own log, exit status and elapsed time. The pool records its
manifest hash and completed-job state separately. One failed member or deadline
stops new admission, blocks its dependents and triggers owned cleanup.

Only explicit read-only `lake --no-cache --no-build --json query` jobs may opt
into `allowed_exits: [0, 3]`. Exit 3 records a stale query, does not satisfy
dependent jobs and returns a non-success pool result. It never counts as a gate
pass. All ordinary jobs require exit 0.

## Controls and interpretation

Run policy tests without starting compiler processes:

```sh
python3 scripts/compilation_pool/test_pool.py
```

When the one global worker is idle, run the lightweight process controls
sequentially and retain their receipts:

```sh
python3 scripts/compilation_pool/test_pool.py --process-tests --process-output /tmp/compile-pool-controls-new
```

They use finite Python children to check ready-job overlap, dependency ordering,
unknown/high-memory exclusivity, reservation admission, failure propagation,
member deadlines, pinned-input mutation and descendant reaping. They do not run
Lean, native exports or independent replay. Actual two-Lean-worker checks and
normal fresh/stale build fixtures require their own coordinator-owned receipts.

Report member outcomes and the one aggregate receipt together. Cached-query
timings, actual elaboration timings and complete verification costs are distinct
measurements. This tool alone establishes no whole-project, cold-build or
independent-kernel-replay speedup.
