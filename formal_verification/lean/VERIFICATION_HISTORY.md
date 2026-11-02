# Verification checkpoints

These are historical results for the stated source snapshots and scopes.
[Verification status](VERIFICATION_STATUS.md) owns the current evidence inventory.

## Current focused validation

The supported-use public theorem, public library root and twelve new regression
theorems compile. The original bigint/control, ROM-shadow and special5
counterexample modules also compile unchanged. The final selected frontend
passes over 3403 modules, 14 concrete Tests modules and five retained Sail modules,
using one worker, with normal Lake no-build source freshness and recomputed
compiled-artifact hashes. No repair builds were needed. This is selected-scope
evidence, not a whole-project assurance snapshot. A prerequisite dependency
rebuild reached the 900-second cap; the later incremental scoped builds passed.
Cold-run feasibility remains unestablished.

Direct independent kernel replay also passes for all six new modules: 192 safe
declarations at a 32 MiB Lean thread stack. Imported modules were not transitively
replayed in that focused check. All 12399 established audit roots are retained,
with ten additional explicit roots. Complete environment auditing and transitive
replay remain separate pending gates.
Focused axiom smoke reports for the contract, bridge and regression roots contain
only propext, Classical.choice and Quot.sound; they do not replace that complete
environment audit.

The helper/trace layer check now passes. HashABI imports circuit-level protocol
modules directly. The round `Airbender.Blake2Round.controlAt` and special5 `Airbender.Keccak.scheduleControl`
definitions moved verbatim into definition-only protocol modules; their public
names and bodies and the remaining caller definitions are preserved. A guarded
normal build of both protocols, HashABI and both caller modules passes (1833
Lake jobs, 11.39 seconds, 521.11 MiB footprint and 2896.70 MiB resident), with no
surviving owned workers. Direct kernel replay also passes for all five changed
modules, covering 60 safe declarations at a 32 MiB Lean thread stack, with
compiled parts unchanged across replay. Imports were not replayed transitively
in this focused check. No production circuit, generator or layout changed.

Linux resource/process controls also pass in a disposable aarch64 container
(Linux 6.10.14-linuxkit, Python 3.12.11): 29 guard tests and 23 compilation-pool
policy/process tests. They exercise anonymous-memory limits, finite process
stack, pidfd/subreaper supervision, detached-descendant cleanup and aggregate
worker limits. These controls do not establish a Linux Lean build, full replay
or cold-cache reproduction.

The full frontend rebuilt the project and concrete Tests sources, then found
late imports in the [direct audit entrypoint](Airbender/Checks/Axioms.lean). All 908
imports now precede commands, preserving their order and every one of the 12409
explicit roots in its original order. The repaired entrypoint compiles (6844
Lake jobs, 19.78 seconds, 960.70 MiB footprint and 4416.84 MiB resident), with no
surviving owned workers. An earlier attempt also stopped at a competing-worker
lock check. Interrupted attempts are not successful assurance snapshots.

The later run completed source freshness for all 4862 modules (219 concrete Tests),
native dependency freshness, library/executable builds, direct axiom comparison,
importer runtime and source/evidence identity checks. Final review exposed two
stale mutation fixtures and a reserved local name in the generated Lean inventory.
The fixtures now forge consistent hash manifests to reach their intended absence
and path checks; production validation is unchanged. All nine snapshot mutation
controls pass. The repaired inventory passes 200 contextual guide references,
190 explicit public Review theorem roots, 1305 links and the layer check (61.25
seconds, 768.65 MiB footprint, 4238.23 MiB resident, no surviving owned workers).
Fifteen assurance policy tests pass.

The final complete source/runtime/review frontend passes at f0b059fe6412:
4862 modules, 219 concrete Tests, five retained Sail modules and native freshness
for 3509 runtime modules, both executables and the library. Normal Lake no-build
freshness, compiled-artifact hashes, direct axiom comparison, importer runtime
and all review checks pass. Its 23 guarded jobs total 260.14 seconds from the
normally built cache, with peak footprint 855.31 MiB, resident 4279.14 MiB and no
surviving owned workers. This is a complete frontend snapshot, not a completed
environment audit or independent transitive replay.

The subsequent Mac environment audit stopped at the unchanged resident cap:
5125.94 MiB against 5120 MiB, footprint 1193.53 MiB, after 125.97 seconds, with no
surviving owned workers. It issued no successful audit result. Remaining assurance
is being attempted in native aarch64 Linux using its documented charged-memory
accounting and the same limits. Cold cache bootstrap exposed a metadata query
counted as a second compiler: Mathlib's initializer invokes `lean --print-prefix`.
Linux now recognizes only that exact query; its memory and time remain charged,
and unknown invocations and two actual compilers still trigger the worker limit.
Linux native freshness now passes at ac90532c92b1: twelve executed generators,
thirteen complete exports, all receipts and 546 native dep-info inputs. The 25
guarded jobs total 242.97 seconds, with peak charged memory 1629.62 MiB and no
surviving owned workers. Both retained/fresh compiler validators and provenance
controls pass; all 67 native compiler export files reproduce byte for byte.
The CI comparison now checks the exact root-file inventory and every byte,
leaving the separate interpretation/lookup directories to their own validators.
Its actual-data check passes and missing, extra and changed export controls reject.
Environment auditing, transitive replay, negative controls and the complete cold
Linux frontend remain pending.

### Prior compiler-composition checkpoint

Native Rust compiler capture regeneration and both retained/fresh production
checks pass: all 67 files reproduce byte for byte. The measured guarded run took
27.06 seconds, with peak footprint 1341.22 MiB and resident memory 1353.02 MiB,
and left no surviving owned workers. This validates the native capture/provenance
step only. Separately, all 14 actual native logical-row compositions compile,
including payload/mask/helper transport, operand coverage and setup bindings.
Program execution, logical execution and the final public compiler theorem module
compile and pass direct selected-module kernel replay at a 32 MiB Lean thread
stack. The final public-wrapper build took 37.49 seconds, with peak footprint
586.75 MiB and resident memory 3093.56 MiB, and left no surviving owned workers.

An isolated fixture using the actual Lake target metadata passes all eight dirty
cases: two setup inputs across four setup-reading test modules. This checks Lake
dependency wiring using a lightweight fixture; it does not execute the actual
setup-test bodies. Separately, the three previously omitted GKR tests, four actual
setup tests, two new regressions and upstream platform compatibility compile and
belong to the completed selected frontend scope.

The final selected frontend passes over a 3279-module import closure containing
10 concrete Tests and five retained Sail modules, using one worker. Project-import
inventory, normal Lake no-build source-freshness queries and recomputed compiled
artifact hashes all pass without repair builds. The run took 96.51 seconds,
with peak footprint 538.71 MiB and resident memory 1585.52 MiB, and left no
surviving owned workers. Source and compiled manifests bind this selected scope;
no full assurance build snapshot was issued. The final upstream-compatibility
build also passes: 670.85 seconds, peak footprint 1589.04 MiB, raw resident memory
4110.22 MiB and no surviving owned workers.

The full environment audit, complete independent dependency replay, transitive
negative controls and cold-run feasibility remain pending. The completed Linux
25-job native setup generator/export freshness gate and the 67-file compiler
capture reproduction check are separate from those proof assurance gates.

The current targeted environment walk of
[the Keccak Iota mapping](Airbender/Review/Circuits/Keccak/Iota.lean)
confirmed constructor/type dependencies on Quot.sound and propext that the direct
report omitted. The [reviewed disposition](scripts/axiom_dispositions.json)
records that standard-axiom baseline correction. This targeted result does not
regenerate the full baseline or establish a complete current-head audit.

## Historical validation evidence

- Full ordinary suite at `5b17af422`: 1,842 modules and 176 concrete Tests passed.
- Before the hash circuit rollback, f099bb549 passed 34 compiler targets and a
  direct 7,766-root axiom report. Direct reports are smoke tests; they do not replace
  the compiled-environment dependency audit or independent replay.
- After rollback, focused native-path/tests and 293 regenerated compiler modules,
  provenance checks and focused direct axiom reports were recorded. These do not
  establish a full current-head suite, native hash enforcement or full replay.

[Detailed evidence history](VERIFICATION_HISTORY.md) ·
[Compiler scope and historical evidence](GKR_COMPILER_VERIFICATION.md) ·
[Reproduce checks](README.md#reproduce)

## Earlier checker implementation log

# Verification status

<!-- source-names: keccak_special5 -->

The model proves all three public machine targets. Each proof includes the
native combined stream relation, public program binding and initialization.
Exact lookup, request and RAM matching remain explicit. The final full
validation is pending.

## Production machine targets

| Setup machine | Current target status |
| --- | --- |
| Unrolled full unsigned | Proved by `MachineTargets.Proofs.unrolled_full_soundness`. The theorem has exactly the `UnrolledFullUnsigned` target type. It includes native execution, public supported-use induction, all three original split setup sources and initialization. It admits the blessed 361-call split Keccak sequence. Exact lookup, request and RAM matching remain explicit. The target excludes special5 calls. |
| Unrolled reduced | Proved by `MachineTargets.Proofs.unrolled_reduced_soundness`. The theorem has exactly the `UnrolledReduced` target type. It includes public program binding, native combined execution and initialization. Exact lookup, request and RAM matching remain explicit. |
| Unified | Proved by `MachineTargets.Proofs.unified_soundness`. The theorem has exactly the `Unified` target type. It includes public program binding, native combined execution and initialization. Exact lookup, request and RAM matching remain explicit. The target excludes special5 calls. |

[The three target definitions](Airbender/Review/Compiler/MachineTargets.lean)
are Lean propositions. Each now has a proof with exactly that target type.
Each target names its native acceptance, program setup, decoder lookup and
initialization premises.
Exact lookup matching and state/RAM permutations remain explicit.

The three target proofs are complete. Work now follows design items 2 and 3.
Native public-program acceptance covers all 14 CPU profiles. Earlier compiler
interfaces remain as compatibility declarations. The public proof graph excludes
captured decoder interpretation and retained-image contracts. The verified
checker rollout remains open. All 22 arithmetic captures now use whole results.
All 22 Clean ideal captures now use complete results.
All 22 wiring captures now use complete results.
All ten Shift prefix columns now use complete results.
Other table families and metadata still need migration. The adopted AND checker
has focused measurements below.

## Verified checker measurements

The AND output certificate now uses one Boolean result for all 898 source
blocks. A proved checker derives the original `ShiftCertificate.and_outputs`
statement. The statement and its premises stay the same. The importer packs
only AND output payloads. It preserves every block constructor, count, stride
and value. The ordinary table, unified slice and both full native setup imports
use the same encoding. No production source or native artifact changes.

The following measurements use Lean 4.31.0 on this Mac. They measure the selected
certificate module with cached imports. They do not measure a cold full build.
The baseline uses the previous data and proof objects. The new result includes
the coverage check and source-binding corollary.

| Selected AND certificate | Previous proof | Packed checker |
| --- | ---: | ---: |
| Lean build | 169.87 s | 2.74 s |
| Exact module kernel replay | 114.67 s | 2.66 s |
| Build peak physical footprint | 1170.95 MiB | 587.93 MiB |
| Replay peak physical footprint | 1378.24 MiB | 1021.62 MiB |

Both replay runs trust their imported objects. The new source group checks all
67 adopted modules. Its last two batches pass in 298.17 s and 112.53 s. They
reuse source and import hash records. Their peak physical footprints are
2075.29 MiB and 1324.07 MiB. The batches also checked two unused equality
prototypes. Those prototypes are outside the adopted source tree.
Selected replay also passes for the block checker, payload proof, closed-form
arithmetic, source binding and public wrapper. This is not transitive replay.

Ten kernel controls cover byte order, a changed byte, an extra payload byte,
affine and periodic blocks, the last row and domain bounds. Direct axiom
checks pass for all 93 new roots and the original output theorem. They use only
`propext`, `Classical.choice` and `Quot.sound`. All 17,599 established roots
remain. That checkpoint has 17,692 explicit roots. The setup pilot adds 71
roots. Its adoption adds six helpers. That checkpoint has 17,769 explicit roots. The column 5 rollout adds 85 roots.
That checkpoint has 17,854 explicit roots. The next three fixed-column
families add 131 roots. That checkpoint has 17,985 explicit roots. The arithmetic pilot adds 38 roots.
The numeric arithmetic rollout adds 434 roots.
The next seven arithmetic families add 1,041 roots.
The packed normalization proof adds 105 roots.
The dense arithmetic rollout adds 925 roots.
The Clean placement rollout adds 497 roots.
The XOR9 rollout adds 244 roots.
The Chi rollout adds 202 roots.
The shift output rollout adds 6,310 roots.
The native OR, XOR and Blake byte-XOR rollout adds 492 roots.
That checkpoint has 28,273 explicit roots.

The complete ordinary AND data has the same serialized values before and
after this change. Its SHA-256 is
`ebf7b9b6fbe4f934af6aea75d5523c70ef1612e9976ea17dda0f06a04b57641d`.
Runtime controls compare both changed full setup columns to their original
JSON blocks. They also compare the native and ordinary AND output columns.
All comparisons pass. These controls check import fidelity; they supply no
proof term. The generator check, mutation control, static scan, boundary
controls and canonical program-graph check pass. No worker remains.

Evidence is in `/tmp/airbender-review-round/checker-pilot-2026-10-31/`.
The setup-column pilot below proves the second fact family. Column 2 now uses
that certificate. The broader rollout remains open. Both cache modes stay
required. The cold full build, full frontend checks, environment audit and
baseline refresh, transitive replay, and Linux runtime and cache qualification
remain pending for implementation review.

### Setup-column pilot

The unified column 2 pilot covers the complete 2,584-block equality family.
Its source span excludes the program ROM region. The target concatenates the
matching XOR, OR and AND spans. A generic codec preserves the original array
constructors and packs literal leaves into byte naturals. A proved Boolean
checker gives exact decoded block equality. One kernel `ok` closes the capture. The same result checks all 21 row-count
conclusions from the established chunk declarations.
Separate kernel bindings connect both encodings to the actual native columns.
They use the existing generic array-layout lemmas to avoid whole-array reduction.

| Selected setup equality family | Six old modules | Three capture modules | Adopted family, four modules |
| --- | ---: | ---: | ---: |
| Lean build | 33.18 s | 22.41 s | 20.29 s |
| Exact module replay, summed | 32.16 s | 8.54 s | 10.37 s |
| Build peak physical footprint | 1101.80 MiB | 856.97 MiB | 860.02 MiB |
| Replay peak physical footprint | 1522.79 MiB | 1278.55 MiB | 1276.91 MiB |

Both sides use retained imports. The new build total includes data generation,
source bindings and the capture proof. The shared codec and reader need one
initial build. Replay checks the three capture modules separately and trusts
their imports. The shared codec also passes selected replay. Full transitive
replay remains pending.

The six new source modules pass focused builds. All 71 direct axiom roots
use only `propext` and `Quot.sound`. Thirteen kernel controls cover
all array recipes, signed strides, changed data and incorrect row counts. The existing CI source
binding control now accepts the exact packed binding and requires a kernel
type mismatch for a changed value. Both focused controls pass. The old RLE
control remains in that gate. It has not rerun for this checkpoint.
The capture and both bindings use default heartbeats. Only the data importer
raises the limit for its complete capture command. Each literal data declaration
holds at most 128 block records. A balanced append tree names the full capture.
The same 15-module source group passes with that representation.

The adopted family includes one public projection module. It replaces all six
old equality shards. It preserves 107 declaration names and all 42 theorem
statements. The prefix assembly proves the exact source and target data
coverage with those projections. Its 15-module focused group passes. Selected
projection replay and 113 preserved-declaration and helper axiom checks pass.
The axiom set stays within the three allowed axioms. Three generator controls
check the public names, reject scope drift before writes, and preserve an
untracked file at a retired path. All equality and prefix generator checks pass.
The declaration origins move to the projection module. The pending environment
audit must record that move. Other setup columns and fact families still need
migration. The broader rollout and final full validation remain open.

### Wide setup-column rollout

Unified equality column 5 now has one checker result for 26,112 native blocks.
The result also checks all 204 established row-count conclusions. The capture
excludes the program ROM region. It includes both fixed source spans and the
matching shift, rotate8 and rotate7 target spans.

A balanced tree holds bounded lists of numeric block records. The checker reads
that tree directly. It checks each branch size before it uses the size to select
rows. The generic soundness theorem gives exact decoded block equality and each
requested row count. Separate kernel proofs bind the trees to the complete native source and target
spans. The tree layouts reuse the existing bounded data. Their proofs use append lemmas and preserve opaque numeric leaves. Native span
data also has at most 128 records per declaration. Balanced map and list
congruence proofs bind those spans. Each typed local equality stays subject to
the kernel check. These changes remove the deep flat conversions from replay. No native value or production source changes.

The three capture modules pass focused source builds. Data and append layouts
take 32.76 s. Native bindings take 63.80 s. The certificate takes 7.28 s.
The binding repair group includes the bounded list helpers and reader. It takes
101.82 s, including 27.57 s of exact binding-module replay. Its peak physical
footprint is 2336.41 MiB. Replay uses the standard 32 MiB Lean thread stack. These runs trust retained imports.

The final 25-module consumer group passes in 155.17 s. Its peak physical
footprint is 2001.47 MiB. It checks both column assemblies, all eight affected
region consumers and all three control modules. It reuses source and import
hash records for unchanged modules. A plain import control also passes.
The earlier flat-list comparisons exceed the existing 2560 MiB footprint limit.
Those comparison variants are outside the adopted source tree.

One projection module replaces 51 old fact modules. It preserves all 1,021
public declaration names and all 408 theorem statement types. Each projection
selects one tree leaf. The same closed checker result also verifies the whole
leaf row counts. The source and target coverage checks remain kernel proofs. Declaration origins move to the
projection module. The pending environment audit must record that move.

Selected replay passes for the shared tree checker, capture data and layouts,
native bindings, capture certificate, public projections, column assembly and
both new control modules. It checks 8 selected modules with cached imports.
The safe declarations have no dependencies on skipped compiler helpers.
This is not transitive replay. All 1,106 direct preserved-declaration and new
root axiom checks pass. They use only `propext`, `Classical.choice` and
`Quot.sound`. All 17,769 established explicit roots remain. Four generator
controls check names, the skipped source gap, scope drift and untracked files.

Six source-binding controls pass. They cover exact flat, balanced and layout
bindings. The kernel rejects a changed value in each form. A later source
check covers the reader, data/layout module and layout control after the
command grammar repair. It passes in 48.68 s, including the six controls.
No worker remains. Full RLE mutation control is outside this focused run.

The broader rollout remains open. Both cache modes stay required. Full frontend
validation, environment auditing and baseline refresh, transitive replay, cold
full measurements, and Linux runtime and cache qualification remain pending.

### Additional fixed columns

The same checker now covers complete fixed equality captures for columns 4, 6
and 7. A shared generator emits their data, append layouts, native bindings and
capture certificates. It rejects a program ROM region or a changed leaf width.
Each capture has one closed kernel result. Public projections select bounded
leaves from that result.

| Unified column | Native blocks | Row-count conclusions | Old fact modules | Preserved declarations | Preserved theorem types |
| --- | ---: | ---: | ---: | ---: | ---: |
| 4 | 25,216 | 197 | 50 | 986 | 394 |
| 6 | 24,064 | 188 | 47 | 940 | 376 |
| 7 | 24,448 | 191 | 48 | 955 | 382 |

One projection module replaces the old fact modules for each column. All 2,881
declaration names and all 1,152 theorem statement types stay the same. Kernel
coverage proofs check both original native sides. The source spans exclude the
program ROM region. Their gaps and target positions stay explicit.

All nine capture modules pass focused source builds. Their three-module totals
are 101.55 s, 92.95 s and 94.70 s. A 46-module consumer group passes in 228.15 s.
Its peak physical footprint is 1938.57 MiB. It includes both adopted columns and
all three new column assemblies and their region consumers. These checks trust
retained imports and reuse source and import hash records for unchanged modules.
The earlier column 6 run stopped on unused simp arguments. The generator now
omits those arguments for single-span captures.

Seven Python generator controls pass. They cover complete fixed scopes,
program-region rejection, one closed result, public names, source gaps, scope
drift and untracked files. All capture, projection and prefix generator checks
pass. CI now runs these checks before native exports. The workflow YAML parses.
The full CI run and Linux qualification remain pending.

All 15 selected replay modules pass with the standard 32 MiB thread stack.
They cover data, native bindings, capture certificates, public projections and
column assemblies. No safe declaration uses a skipped compiler helper.
The replay and axiom group takes 147.78 s. Its peak physical footprint is
2359.13 MiB. All 3,012 direct axiom checks pass. The axiom set stays within
`propext`, `Classical.choice` and `Quot.sound`. Imported objects remain trusted
in these selected replay runs. Full transitive replay remains pending.
No worker remains.

That checkpoint retains all 17,854 established roots and adds 131 roots. Declaration origins move from the old modules to the projection
modules. The environment audit and baseline refresh remain pending. The wider
fact-family rollout remains open.

### Arithmetic pilot

Both AddSub captures now have one closed kernel checker result. The checker
proves address uniqueness, input projection, all source and forward polynomial
identities, and every gate check. Generic soundness proofs derive the original
Boolean facts. The original finalizer and public soundness statements stay the
same. Numeric address keys replace repeated address comparisons. Proved Boolean
polynomial comparisons preserve the original normalizer result.

This pilot removes 10 fact modules. The two captures now use four modules,
including their data foundations. No pilot module raises `maxHeartbeats`.
The kernel accepts all 338 old public theorem types against the new proofs.
All 158 imported public data values are identical. All 496 public declarations
remain. The checker adds two capture declarations. Data and circuit equations
do not change.

The following measurements use cached imports on this Mac. Each previous proof
uses six modules. Each new proof uses one. The common data foundations and the
shared checker modules are outside these per-capture times.

| Capture | Previous build | New build | Previous selected replay | New selected replay |
| --- | ---: | ---: | ---: | ---: |
| AddSub uncached | 12.24 s | 4.77 s | 11.46 s | 3.18 s |
| AddSub cached | 12.32 s | 5.46 s | 11.62 s | 3.30 s |

The eight-module source group passes in 25.47 s. Its peak physical footprint is
755.66 MiB. Four direct functional and clean-arithmetic consumers also pass.
Selected replay passes for both capture modules and all three shared checker
modules. Replay uses the standard 32 MiB thread stack and trusts imports.
No safe replay declaration depends on a skipped helper. All 534 direct axiom
controls pass. They use only `propext`, `Classical.choice` and `Quot.sound`.
Seven kernel controls check an identity, address constructors, duplicate
addresses, missing backward and forward witnesses, a changed gate and a changed
input projection. All pass. Ten Python generator controls pass. CI checks both
pilot captures. All 17,985 established explicit roots remain. The inventory
now has 18,023 roots.

The broader `GKRProtocol` import check does not pass with retained objects. It
reports duplicate ownership of
`Airbender.WordMemory.importedConstraintsTraceColumns.eq_1`. A control with the
previous arithmetic objects reports the same WordMemory import collision. The
final frontend rebuild and environment audit must resolve this cache state.
This checkpoint does not claim that the aggregate import passes.

The earlier typed Blake round check exceeded the 2560 MiB footprint limit.
Conversion at check time did not remove that cost. The numeric rollout below
replaces those unadopted variants. Other arithmetic captures still need migration.

### Numeric arithmetic rollout

Both Blake round captures use direct numeric data. Separate kernel equalities
bind all source expressions, lowered residuals, computed extensions and
certificate rows to the original imports. Further bindings check normalized
source rows, both normalized gate sides and sorted address keys. The exporter
supplies untrusted numbers. Its hashes supply no proof.

For regeneration, first use `gkr_full_arithmetic_certificate.py` with
`--family blake-round --foundations-only --write`. Rebuild those two foundations
with the serial builder. Then run `gkr_numeric_arithmetic.py --write`. Finally,
run the full arithmetic generator with `--family blake-round --write`. The
normal `--check` gate requires complete payload provenance and dimensions.

Bounded leaves hold at most 16 rows. The flat payload and the lookup tree share
those leaves. The kernel checks each complete tree layout and each branch size.
The checker reads the materialized trees. It does not rebuild a tree for each
lookup. It reuses the bound source normal forms for unit certificate rows.
A proved equality preserves the original comparison, including its fallback
for other factors and noncanonical coefficients.

Each capture has one closed kernel result. Generic soundness derives the exact
original `FullArithmeticChecks.check` statement. All old per-index declarations
remain as corollaries. A direct adapter derives the aggregate public facts from
the same result. It avoids the old finite aggregate assembly.

The rollout retires 84 old fact modules. Both captures now use ten modules in
total, including the two original data foundations. No capture module raises
`maxHeartbeats`. The numerical circuit data and production Rust stay the same.

The following source measurements use retained imports on this Mac. They
include data bindings and all public corollaries. They exclude the unchanged
data foundations and the shared checker modules.

| Blake round capture | Four capture modules | Closed kernel result | Selected result replay |
| --- | ---: | ---: | ---: |
| Cached | 65.67 s | 8.10 s | 8.19 s |
| Uncached | 56.97 s | 7.70 s | 7.44 s |

The source and selected result replay group passes in 145.73 s. It peaks at
2433.97 MiB. Replay uses the standard 32 MiB thread stack. Both source
foundations pass with default heartbeats. Both AddSub public modules and four
direct Blake functional and clean arithmetic consumers also pass. These checks
trust retained imports. They do not constitute a cold build or transitive replay.

The kernel accepts all 3,169 original Blake public theorem types. All 929
imported public data values are identical. All 4,098 original declarations
remain. The same control still accepts all 338 AddSub theorem types and all
158 original AddSub data values.

All 16 selected replay modules pass. They cover the five shared checkers,
both Blake data, binding, result and public modules, both AddSub public modules
and the numeric controls. No safe declaration uses a skipped dependency.
The preservation, mutation, axiom and selected replay group takes 148.61 s.
It peaks at 2169.89 MiB. These runs trust imported objects. Full transitive
replay remains pending.

All 4,532 direct axiom checks pass. They use only `propext`, `Classical.choice`
and `Quot.sound`. Kernel controls cover coefficients, variables, monomial
order, missing witnesses, changed normal forms, gates, duplicate keys and
forged tree sizes. Five exact binding and proof controls pass. The kernel
rejects all five changed controls. All 14 Python generator controls pass.
Generation, provenance, boundary, program graph and workflow syntax checks
pass. CI checks both capture modes and runs the kernel binding controls after
the Lean source build. All 18,023 established explicit roots remain. The
inventory now has 18,457 roots. No worker remains.

### Additional arithmetic families

The same numeric checker now covers both cache modes for Blake G, jump and
branch, MUL/DIV, shift and binop, subword memory, unified and word memory.
Each capture uses one closed kernel result. The public corollaries retain their
original types. All original input, source, residual, extension and certificate
values stay the same.

This step retires 108 fact modules. The fourteen captures now use 70 modules,
including their original foundations. All 70 source modules pass in 222.45 s.
The group peaks at 707.83 MiB. No adopted capture raises `maxHeartbeats`.

A kernel control accepts all 3,723 original public theorem types. All 1,645
imported data values are identical. All 5,368 original public declarations
remain. All 6,409 focused axiom checks pass. They use only `propext`,
`Classical.choice` and `Quot.sound`.

All 56 selected replay modules pass with the standard 32 MiB thread stack.
No safe declaration uses a skipped dependency. The preservation, axiom and
replay group takes 134.39 s. It peaks at 1161.71 MiB. These runs trust imported
objects. They do not constitute transitive replay.

All 14 Python generator controls pass. Generation, payload provenance,
boundary, public program graph, links and workflow syntax checks pass. CI
requires all 22 arithmetic captures. Eighteen captures now use whole results.
Bigint and Keccak still use their established proofs in both cache modes.
All 18,457 established explicit roots remain. The inventory now has 19,498
roots. No worker remains.

### Dense arithmetic rollout

The initial dense path exceeded the memory cap. Bigint has 5,064 raw source
terms. A direct source binding exceeded the cap. An erasure prototype retained
every term before polynomial expansion. Its four complete source bindings passed
source checks and selected replay. That group peaked at 1755.77 MiB. The whole
Bigint checker still exceeded the cap. The packed trace step below removes that
remaining normalization cost.

The expression-erasure prototypes stay in
`/tmp/airbender-review-round/checker-pilot-2026-10-31/dense-normalization-prototype/`.
The adopted source bindings below use the proved erasure theorem.

#### Packed normalization proof

A proved packed trace checker closes the numeric normalization resource
obligation. It stores bounded terms in base-2^64 words. Each trace gives an
insertion position and the next packed result. The checker verifies both
neighbor keys, the position bound and the complete next result. The soundness
proof derives sortedness from the preceding checked state. It proves exactly
`NumericPolynomialChecks.normalize p input = expected`. It requires exact input
and output encodings, monomial bounds and coefficient bounds. Each capture must
prove those bindings in the kernel.

The four shared proof modules and their control module pass source checks and
selected replay. That group takes 16.54 s. It peaks at 745.08 MiB. All modules
use default heartbeats. The discarded whole-normalization variants remain
outside the source tree.

Four numeric pilots cover the complete backward and forward residual banks.
They use both cache modes. The following results use retained imports and the
standard 32 MiB replay stack. They do not include native binding qualification.

| Numeric pilot | Result build | Result replay |
| --- | ---: | ---: |
| Bigint cached | 2.81 s | 2.90 s |
| Bigint uncached | 2.58 s | 2.71 s |
| Keccak cached | 2.65 s | 2.80 s |
| Keccak uncached | 2.40 s | 2.53 s |

All 13 selected replay modules pass. No safe declaration uses a skipped
dependency. All 105 focused axiom checks use only the three allowed axioms.
Ten exact controls pass. The kernel rejects all ten changed certificates.
The controls cover positions, inputs, outputs, trace coverage, lengths, word
bounds and modulus bounds. Generation, boundary, program graph, link and
workflow syntax checks pass. The final full validation did not run.

At that checkpoint, the four arithmetic captures still used their established
proofs. The numeric pilots stayed outside the adopted source tree. The audit
inventory retained all 19,498 established roots and added 105 proof and control
roots. The next step adopts the complete native bindings and public corollaries.

#### Dense capture adoption

Both Bigint captures and both Keccak captures now use the packed trace checker.
Separate kernel proofs bind the source expression trees before expansion.
The proofs retain all zero terms, coefficient values and variable order.
Other bindings cover every residual, extension and certificate entry. The trace
binding checks the complete backward and forward banks. The soundness theorem
derives the original `FullArithmeticChecks.check` result. Each public per-index
fact remains a corollary with its original statement.

All 22 arithmetic captures now use whole checker results. Both cache modes
remain required. This step retires 85 fact modules. The four captures use 24
modules, including their four original foundations. None raises `maxHeartbeats`.

The 29-module source and selected replay group passes in 669.48 s. It peaks at
2404.69 MiB. The remaining control module also passes source and replay.
All 30 selected replays use the standard 32 MiB thread stack. No safe declaration
uses a skipped dependency. These runs trust imported objects. They do not
constitute transitive replay.

A kernel control accepts all 3,335 original theorem types. All 1,383 imported
data values are identical. All 4,718 original public declarations remain.
All 5,643 focused axiom checks pass. They use only `propext`, `Classical.choice`
and `Quot.sound`. Eleven exact controls pass. The kernel rejects all eleven
changed certificates or bindings. All 17 Python generator controls pass.
The preservation, axiom and mutation group takes 56.29 s. It peaks at 823.77 MiB.

All eight direct functional and clean consumers pass source checks in 43.32 s.
They peak at 443.28 MiB. Generation, provenance, boundary, public program graph,
link and workflow syntax checks pass. The full aggregate import remains subject
to the previously recorded cache ownership issue.

The audit inventory retains all 19,603 established roots and adds 925 roots.
The current inventory has 20,528 roots. Evidence stays in
`/tmp/airbender-review-round/checker-pilot-2026-10-31/`.

Both cache modes remain required. Other fact families and unlimited heartbeat
settings also need migration. The full frontend, environment audit and baseline
refresh, full transitive replay, cold full measurements, and Linux runtime and
cache qualification stay pending for implementation review.

### Clean placement rollout

All 22 Clean placement captures now use one numeric checker result each.
A proved checker validates bank coordinates and complete address coverage.
Kernel equalities bind the numeric data to the original address bank and
placement list. Address-code injectivity gives the original placement
round trips. Every per-address statement remains a corollary with its old type.
Both cache modes remain required.

This step changes only the placement fact family. The Clean per-statement
ideal checks remain unchanged. Their separate migration remains open.
The new capture modules use default heartbeats. The existing Clean arithmetic
modules retain their finite limit for those ideal checks.

All 44 capture and consumer modules pass source checks and selected replay.
The rollout batch takes 732.15 s. It peaks at 1714.27 MiB. The earlier pilot
and shared-module group takes 150.69 s. It peaks at 1186.79 MiB.
All 47 selected replays use the standard 32 MiB thread stack. No safe declaration
uses a skipped dependency. These runs trust imported objects.

A kernel control accepts all 7,684 original theorem types. All 3,836 imported
data values are identical. All 11,520 original public declarations remain.
All 12,017 focused axiom checks pass. They use only `propext`, `Classical.choice`
and `Quot.sound`. Six exact controls pass. The kernel rejects all six changed
results or bindings. The preservation, axiom and mutation group takes 29.26 s.
It peaks at 869.43 MiB. All 20 Python generator controls pass.

Generation, proof boundary, public program graph, link and workflow syntax
checks pass. CI requires the placement mutation controls. The audit inventory
retains all 20,528 established roots and adds 497 roots. It has 21,025 roots.
Evidence stays in `/tmp/airbender-review-round/checker-pilot-2026-10-31/`.

Other fact families and unlimited heartbeat settings still need migration.
The aggregate import remains subject to the recorded cache ownership issue.
The full frontend, environment audit and baseline refresh, full transitive
replay, cold full measurements, and Linux runtime and cache qualification
stay pending for implementation review.

### Complete XOR9 table

The complete native XOR9 output now uses one numeric checker result.
The checker covers all 2,050 blocks and all 64 established extent requests.
It reads packed 16-bit words. A generic signed-run proof handles positive and
negative strides. Packed masks check every seed and signed endpoint. The
soundness proof derives the original validity predicate. It does not add an
assumption about the data.

Kernel equalities bind each bounded data leaf to its original native block
list. A balanced equality binds the complete column. The public wrapper derives
all original output and extent statements as corollaries. The original finalizer
still proves complete column coverage. This step retires 65 proof modules.
The four capture modules include the unchanged partition data. They have no
unlimited heartbeat setting. The number of `Proofs/` files with that setting falls from
151 to 85. Other fact families still need migration.

| Selected XOR9 component | Source build | Selected replay |
| --- | ---: | ---: |
| Packed data and exact source bindings | 48.22 s | 41.61 s |
| Closed checker result | 3.17 s | 3.43 s |
| Public corollaries and finalizer | 7.85 s | 3.71 s |

The final six-module source and replay batch takes 121.99 s. It peaks at
2122.10 MiB. The other two shared modules also pass source and replay.
All eight selected replays use the standard 32 MiB thread stack. No safe
declaration uses a skipped dependency. These runs trust imported objects.
They do not measure a cold full build or full transitive replay.

A kernel control accepts all 192 original theorem types. All 193 imported data
values are identical. All 385 original public declarations remain. All 629
focused axiom checks pass. They use only `propext`, `Classical.choice` and
`Quot.sound`. Eleven exact controls pass. The kernel rejects all eleven changed
results or source bindings. These controls include a packed borrow, a high seed,
a large stride extent, the stride sign, the final row and a changed source word.
The qualification group takes 45.65 s. It peaks at 807.51 MiB.
The direct XOR certificate consumer passes source and selected replay.
All 24 Python generator controls pass. CI requires capture freshness and the
kernel mutation controls.

The audit inventory retains all 21,025 established roots and adds 244 roots.
It has 21,269 roots. The declaration origins of the retired shards move to the
public wrapper. The deferred environment audit must record that change.
Evidence stays in `/tmp/airbender-review-round/checker-pilot-2026-10-31/`.
The final full validation remains pending for implementation review.

### Complete Chi table

The complete native Chi output now uses one packed checker result.
It covers all 898 original blocks. A shared byte-table checker handles AND, OR,
XOR and Chi. Its soundness theorem derives the original output equations.
The capture reuses the proved signed-word codec and packed endpoint checks.
Separate kernel equalities bind every source leaf and the complete column.
The public Chi theorem keeps its original name and type.

The five-module source and selected replay batch passes in 35.01 s. It peaks at
1250.59 MiB. The closed result takes 2.10 s to build and 2.03 s to replay.
The test module also passes source and replay. The direct fixed-table consumer
passes source and replay in 15.94 s. It peaks at 1549.39 MiB. All seven selected
replays use the standard 32 MiB thread stack. No safe declaration uses a skipped
dependency. These runs trust imported objects.

A kernel control accepts all eight original theorem types. It includes the
six shared block equations. All 21 original imported data values are identical.
All 29 original public declarations remain. Six exact controls pass. The kernel
rejects all six changed operations, source words, strides or bounds.
All 231 focused axiom checks pass. They use only `propext`, `Classical.choice`
and `Quot.sound`. The first axiom query omitted the XOR adapter import.
The corrected query passes. All 27 Python generator controls pass.
CI requires capture freshness and the kernel mutation controls.

The Chi and XOR wrappers now use default heartbeats. This removes both
unlimited settings from `Proofs/Keccak`. There are 83 `Proofs/` files with
unlimited settings. Other fact families still need migration.
The audit inventory retains all 21,269 established roots and adds 202 roots.
It has 21,471 roots. Evidence stays in
`/tmp/airbender-review-round/checker-pilot-2026-10-31/`.
The final full validation remains pending for implementation review.

### Complete shift output columns

All four native shift output columns now use complete packed checkers.
They cover 97,918 source blocks and 1,048,576 output cells.
Exact kernel equalities bind all source leaves and all numeric requests.
The balanced tree checker proves that the packed data has the original values.
Each reference check covers all requests for one column.
The original 64 facts remain as corollaries. All four finalizers remain.
The rollout removes 64 proof modules and 76 unlimited heartbeat settings.
Seven `Proofs/` files still have unlimited settings.

The reference keeps every original control. This includes signed right shifts,
byte reversal and invalid controls. Kernel results bind all 128 basis rows and
all 4,096 packed byte rows to that reference. Generic OR distribution and
proved basis disjointness justify the numeric row sums. A proved span checker
derives the original output equations. No new proof premise was added.

All 44 selected modules pass source checks and kernel replay.
Each replay uses the standard 32 MiB thread stack. No safe declaration uses a
skipped dependency. These runs trust imported objects. The capture and test batch has 30 modules.
It takes 594.42 s. It peaks at 1865.42 MiB of physical memory.
The direct consumer for shift rows also passes source and replay.

All 222 original public declarations remain. A kernel control accepts all 142
original theorem types. All 80 imported data values are identical.
All 6,532 focused axiom checks pass. They use only `propext`,
`Classical.choice` and `Quot.sound`. Eighteen exact controls pass.
The kernel rejects all eighteen mutations. They cover native codecs, request
fields, row bindings, signed fill, invalid controls and domain bounds.
All 32 Python controls pass. Generator freshness and workflow syntax pass.
CI requires the new freshness and kernel mutation checks.

Direct scalar checks and whole packed comparisons exceeded the memory cap.
Bounded spans with computed reference rows also exceeded the cap.
These variants are not adopted. The adopted checks use literal numeric requests
and a balanced lookup of packed rows. Kernel bindings prove each connection.
Each qualification guard cleaned its owned workers.

The inventory has 27,781 roots. It retains all 21,471 established roots.
The old shard declarations now belong to the public wrappers.
The deferred environment audit must record that change.
Evidence stays in `/tmp/airbender-review-round/checker-pilot-2026-10-31/`.
Other item 3 families remain open. These include OR, XOR, coverage metadata,
Clean ideal checks and wiring. Full frontend validation, environment audit,
baseline refresh, full transitive replay, cold full measurements and Linux
runtime and warm cache qualification remain pending for implementation review.

### Complete OR and XOR tables

The native OR, native XOR and Blake byte-XOR tables now use complete packed
checkers. Each capture has one closed kernel result. The shared soundness
proof derives the original output theorem. Exact kernel bindings cover all
source blocks. The three captures cover 2,695 blocks and 196,608 output cells.
No elaborator split computes the per-row facts.

All 38 original public declarations remain. A kernel control accepts all 14
original theorem types. All 24 imported values are identical. All 530 focused
axiom checks pass. They use only `propext`, `Classical.choice` and `Quot.sound`.
Six exact controls pass. The kernel rejects all six mutations.
All 13 selected modules pass source checks and kernel replay.
Each replay uses the standard 32 MiB thread stack. No safe declaration uses a
skipped dependency. These runs trust imported objects.
The binary, rotate-row and shift-row consumers pass source and replay.

The native OR and XOR source and replay batch takes 55.92 s.
It peaks at 1249.29 MiB of physical memory. The Blake byte-XOR source checks
and selected replays also pass. Its closed result takes 2.35 s to build and 2.30 s to replay.
Generator freshness, all 32 Python controls and workflow syntax pass.
CI requires the complete capture freshness check.

The shift coverage module now passes with default heartbeats.
No `Proofs/Tables` file has an unlimited setting.
Four `Proofs/UnifiedReduced` files still have unlimited settings.
A whole metadata checker exceeded the memory cap after the three table
checks passed. It is not adopted. Its source stays in the evidence directory.
The coverage facts still need a checker migration. Each guard cleaned its
owned workers.

The inventory has 28,273 roots. It retains all 27,781 established roots.
Evidence stays in `/tmp/airbender-review-round/checker-pilot-2026-10-31/`.
Other table families, metadata, Clean ideal checks and wiring remain open.
Full frontend validation, environment audit, baseline refresh, full transitive
replay, cold full measurements and Linux runtime and warm cache qualification
remain pending for implementation review.

### Complete Clean ideal captures

All 22 Clean arithmetic captures now use complete checker results.
Both cache modes remain required. The shared soundness theorem derives the
original typed ideal facts and input scope facts. Exact kernel bindings cover
all expressions, gate residuals and witnesses. They preserve every term.

Bigint and Keccak use the proved packed normalization traces. Bounded source
bindings connect the original expressions to direct numeric rows.
The trace checker verifies each insertion position and each complete next state.
BlakeRound uses indices through 674. It exceeds the packed quadratic bound.
BlakeRound and Unified therefore use direct numeric rows and the proved fast
normalizer. The packed codec stays unchanged. Each capture has one complete
semantic result. All old per-statement facts follow as corollaries.

All 11,520 original public declarations remain. A kernel control accepts all
7,684 original theorem types. All 3,836 imported values are identical.
All 18,409 focused axiom checks pass. They use only `propext`,
`Classical.choice` and `Quot.sound`. Seventeen exact controls pass.
The kernel rejects all seventeen mutations. Eleven Python generator controls
pass. Capture freshness and the original scaffold check pass for all 22 captures.
CI requires the numeric capture freshness check and the kernel controls.

All 90 selected modules pass source checks and kernel replay.
Each replay uses the standard 32 MiB thread stack. No safe declaration uses a
skipped dependency. These checks trust imported objects.
The final 68-module source and replay batch takes 649.59 s.
It peaks at 1701.01 MiB of physical memory. The cached Bigint and BlakeRound
groups also pass. The successful source and replay groups peak at 1735.32 MiB.
Each guard cleaned its owned workers.

Direct whole expression checks exceeded the cap for Bigint and BlakeRound.
They are not adopted. Direct numeric rows avoid that aggregate expansion cost.
The first axiom query used incorrect names for the new trace leaves.
The corrected inventory and all focused queries pass.
All 22 former large heartbeat overrides are gone from the Clean capture roots.

The inventory has 35,162 roots. It retains all 28,273 established roots.
Evidence stays in `/tmp/airbender-review-round/checker-pilot-2026-10-31/`.
Wiring, remaining table families and metadata still need migration.
The rotation checkpoint below removes the last four unlimited heartbeat settings.
No production circuit or Rust file changed. Full frontend validation,
environment audit, baseline refresh, full transitive replay, cold full
measurements and Linux qualification remain pending for implementation review.

### Complete wiring captures

All 22 wiring captures now use complete checker results.
Both cache modes remain required. Numeric producer key trees replace repeated
producer scans. Exact kernel bindings cover both complete key banks.
A structural merge sort has a proved permutation theorem. The checker derives
the original `Wiring.check` result. The original soundness theorem and finalizer remain.

All 17,814 original public declarations remain. A kernel control accepts all
12,960 old theorem types. All 4,854 imported values are identical.
All original per-index facts follow as corollaries. The rollout retires 258
proof shards. It keeps the two established import compatibility modules.
All 44 former large heartbeat overrides are gone from the data and Native roots.
The importer parses each complete capture once. The kernel checks each closed
corollary against its original declared type. The declaration API skips no checks.

All 118 selected modules pass source checks and kernel replay.
Each replay uses the standard 32 MiB thread stack. No safe declaration uses a
skipped dependency. These checks trust imported objects.
The 94-module data and certificate stage takes 412.49 s.
It peaks at 1477.25 MiB of physical memory. The 24-module interface stage takes
435.23 s. It peaks at 797.64 MiB. Each guard cleaned its owned workers.

All 18,051 focused axiom checks pass. They use only `propext`,
`Classical.choice` and `Quot.sound`. Ten exact controls pass.
The kernel rejects all ten mutations. Seven Python generator controls pass.
Both complete capture and scaffold freshness checks pass for all 22 captures.
CI requires capture freshness and the kernel controls. Workflow syntax passes.

Direct whole wiring checks and insertion-sort source bindings exceeded the
memory cap on BlakeRound. They are not adopted. The structural sort and
numeric key trees pass the same limit.

The inventory has 53,191 roots. It retains all 35,162 established roots.
Evidence stays in `/tmp/airbender-review-round/checker-pilot-2026-10-31/`.
The original 304 module objects remain in its `wiring-original-oleans` directory.
Remaining table families and metadata still need migration.
Four `Proofs/UnifiedReduced` files still have unlimited heartbeat settings.
No production circuit or Rust file changed. Full frontend validation,
environment audit, baseline refresh, full transitive replay, cold full
measurements and Linux qualification remain pending for implementation review.

### Complete rotation reference grid

One kernel result now checks all 4,096 rotation-byte cases.
The generic finite-grid soundness theorem derives the original public reference.
Exact kernel bindings connect the full rotate8 and rotate16 output columns.
The shared fixed-data equalities remain unchanged.
The last four unlimited heartbeat settings are gone from `Proofs/`.

All eight original public declarations remain. A kernel control accepts all five
old theorem types. All three imported values are identical.
Three small bound helpers retain names used by the old theorem types.
All seven selected modules pass source checks and kernel replay.
Each replay uses the standard 32 MiB stack. No safe dependency is skipped.
The source group peaks at 939.15 MiB of physical memory.
The final qualification takes 28.55 s and peaks at 1783.81 MiB.
Its guard leaves no owned worker.

All 22 focused axiom checks use only the three allowed axioms.
Four exact controls pass. The kernel rejects all four mutations.
CI requires these controls. The inventory has 53,208 roots.
It retains all 53,191 established roots. Generator freshness passes.
The inventory generator now uses a set for repeated root lookups.
This removes a quadratic scan and preserves the generated inventory.
The remaining setup span and table metadata families still need migration.
The final full validation remains pending for implementation review.

### Complete Shift prefix captures

All ten Shift prefix columns now use complete checker results.
The numeric normalizer has a proved binding to the original block normalizer.
It checks complete normalization and row-count requests.
Exact kernel bindings cover all source and target block lists.
The original per-index facts follow from the complete results.

All 18,928 original public declarations remain. A kernel control accepts all
11,874 old theorem types. All 7,054 imported values are identical.
The rollout retires 105 proof shards. Each column now uses five capture modules.
All ten native assembly modules pass with default heartbeats.
Only the capture data modules raise their heartbeat limit.
Comments explain these data limits.

All 65 selected modules pass source checks and kernel replay.
They include both direct Shift consumers. Each replay uses the standard
32 MiB stack. No safe dependency is skipped. These checks trust imported objects.
The 30-module rollout batch takes 401.48 s and peaks at 2054.10 MiB.
The final qualification takes 100.55 s and peaks at 1067.41 MiB.
Both guards leave no owned worker.

All 23,916 focused axiom checks use only the three allowed axioms.
Four normalization controls pass. The kernel rejects all four mutations.
The existing flat, balanced and layout binding controls pass.
The kernel also rejects the retained RLE mutation.
Three generator controls pass. Capture, assembly and inventory freshness pass.
CI requires the complete capture controls and freshness checks.
Workflow syntax and changed-source static checks pass.

The importer caches each parsed region within one capture command.
It keeps the complete fidelity check for that region.
Its contextual DSL words permit ordinary `column` and `region` variables.
An early checker variant exceeded the memory cap during selected replay.
The adopted checker first tests exact input equality. Its soundness theorem
derives the original normalization statement in both branches.

The inventory has 59,782 roots. It retains all 53,208 established roots.
The original 115 module objects remain in `shift-prefix-original-oleans`
under the evidence directory. Other setup span and table metadata families
still need migration. No production circuit or Rust file changed.
Full frontend validation, environment audit, baseline refresh, full transitive
replay, cold full measurements and Linux qualification remain pending for review.

### Complete fixed rotation boundary

The unified column 1 rotation boundary now uses one complete kernel result.
It covers 262,144 source rows and all twelve target blocks.
The scope includes only fixed table regions 47 through 51.
It excludes program ROM. A generator control rejects a program-region change.

The numeric getter has a proved binding to every original array recipe.
The span checker derives the original length and `blockTargetsFollow` facts.
It uses numeric getters for finite boundaries. It proves affine and aligned
periodic spans with their original equations.
The public `follows14` and `length14` statements remain unchanged.
All 28 original declarations remain. A kernel control accepts both old theorem
types. All 26 imported values are identical.

All nine selected modules pass source checks and kernel replay.
They include the direct column 1 prefix consumer. Every replay uses the
standard 32 MiB stack. No safe dependency is skipped.
The five-module capture group takes 27.22 s and peaks at 919.69 MiB.
The closed checker takes 2.10 s to build and 2.07 s to replay.
The consumer group takes 34.13 s and peaks at 1379.26 MiB.
The final qualification takes 26.61 s and peaks at 821.74 MiB.
These checks trust imported objects. All guards clean their owned workers.

All 71 focused axiom checks use only the three allowed axioms.
Six exact controls pass. The kernel rejects all six mutations.
The fixtures cover all nine array recipes, signed strides, missing rows
and source bounds. Three generator controls pass.
Capture, interface and inventory freshness pass. CI requires these controls.
The inventory has 59,827 roots. It retains all 59,782 established roots.
The old unit has no heartbeat override. Its new data importer has a stated limit.

Other fixed setup spans and table metadata still need migration.
The final full validation remains pending for implementation review.

### Complete Shift output extents

All four Shift output extent families now use complete numeric checks.
Each check covers all sixteen original partitions.
The checker uses the adopted packed source encodings.
Exact bindings assemble each partition from its existing source leaves.
The public extent and coverage statements stay the same.
All 68 original theorem types pass a kernel preservation control.
The source partitions and imported encoding values do not change.

All fifteen selected modules pass source checks and kernel replay.
They include all four public output finalizers and the column coverage consumer.
Each replay uses the standard 32 MiB stack. No safe dependency is skipped.
The rollout batch takes 43.74 s and peaks at 1598.70 MiB.
The consumer batch takes 43.94 s and peaks at 1084.93 MiB.
The final qualification takes 20.37 s and peaks at 1159.21 MiB.
These checks trust imported objects. All guards clean their owned workers.

All 213 focused axiom checks use only the three allowed axioms.
Four exact controls pass. The kernel rejects all four mutations.
A raw literal binding mutation exceeded the memory cap.
The adopted control tests a dropped binding and stays within the cap.
Three generator controls preserve the public contracts and untracked files.
Capture and inventory freshness pass. CI requires these controls.
The inventory has 59,972 roots. It retains all 59,827 established roots.
The old per-part literal simplification proofs are gone.
Other fixed setup spans and table metadata still need migration.
The final full validation remains pending for implementation review.

### Complete fixed unified special spans

Six unified columns now use complete fixed special-span checks.
Columns 2, 3, 4, 5, 6 and 7 cover 1,296 source groups.
Each column has one closed kernel result. The checker proves the original
source lengths and `blockTargetsFollow` statements.
The scope excludes groups that touch program ROM or the suffix boundary.
Their original proofs stay in the retained source files.

All 29,908 original declarations remain. A kernel control accepts all 18,367
old theorem types. All 11,541 imported data values are identical.
The rollout retires 158 fixed proof shards.
The data declarations keep their original names and expressions.
The native and length assemblies use the new public projections.

All 73 selected modules pass source checks and kernel replay.
They include 42 consumers and all six complete native prefix columns.
Each replay uses the standard 32 MiB stack. No safe dependency is skipped.
The remaining capture batch takes 243.16 s and peaks at 864.52 MiB.
The consumer batch takes 452.99 s and peaks at 1592.48 MiB.
The final qualification takes 73.47 s and peaks at 879.96 MiB.
These checks trust imported objects. Every guard cleans its owned workers.

All 36,443 focused axiom checks use only the three allowed axioms.
Eight exact span and binding controls pass.
The kernel rejects all eight mutations. Three generator controls pass.
They check the fixed scope, retained program proofs and untracked files.
Capture, length, consumer and inventory freshness pass.
Changed-source static checks and workflow syntax pass.
The inventory has 66,507 roots. It retains all 59,972 established roots.
The 224 original module objects stay in `fixed-special-original-oleans`
under the evidence directory.

Other table metadata and fixed setup families still need migration.
The final full validation remains pending for implementation review.

### Complete fixed unified column-one spans

One closed kernel result covers the 30 remaining fixed source groups in
unified column 1. The separate rotation-boundary capture covers source 14.
Sources 12, 13 and 33 touch program ROM or the suffix. Their proofs remain.
The rollout retires 23 fixed proof shards. The native prefix assembly imports
the complete capture and the four retained unit modules.

All 497 original declarations remain. A kernel control accepts all 256 old
theorem types. All 241 imported data values are identical.
All six selected modules pass source checks and kernel replay. They include
the complete native column-one prefix consumer. Each replay uses the standard
32 MiB stack. No safe dependency is skipped. These checks trust imported objects.

The source and replay batch takes 70.70 s and peaks at 1377.01 MiB.
The closed checker builds in 1.88 s and replays in 1.91 s.
The final qualification takes 43.42 s and peaks at 822.98 MiB.
Both guards clean their owned workers.
All 654 focused axiom checks use only the three allowed axioms.
Ten exact span and binding controls pass. The kernel rejects all ten mutations.
Three generator controls check complete scope, scope drift and untracked files.
Capture, interface, assembly and inventory freshness pass.
The inventory has 66,664 roots. It retains all 66,507 established roots.
The 28 original module objects stay in `column1-fixed-original-oleans`
under the evidence directory.

Other table metadata and fixed setup families still need migration.
The final full validation remains pending for implementation review.

### Complete Shift coverage metadata

The 50 public Shift and binary coverage cases now use the complete native
prefix checkers. Ten Shift length projections sum named region-part facts.
The 40 binary projections use the existing native region-length facts.
The public wrappers select these proofs. They do not compute table literals.
One closed kernel result checks all seven native offsets.
The original three public theorem types pass the kernel preservation control.
No imported data value changes.

All three selected modules pass source checks and kernel replay. They include
the direct imported Shift row consumer. Each replay uses the standard 32 MiB
stack. No safe dependency is skipped. These checks trust imported objects.
The source and replay batch takes 16.51 s and peaks at 1102.29 MiB.
The public coverage module builds in 3.01 s and replays in 2.06 s.
All 16 focused axiom checks use only the three allowed axioms.
Four exact controls pass. The kernel rejects all four mutations.
Three generator controls pass. They preserve complete coverage, the public
contracts and untracked files. Capture and inventory freshness pass.
The source import graph has no cycle.
The inventory has 66,677 roots. It retains all 66,664 established roots.

Direct whole checks over typed table values exceeded the memory cap.
Full-value bindings and direct length-list bindings also exceeded the cap.
The structural extractor prototype stays outside the branch. It did not
qualify. The adopted projections reuse the existing complete checks.
Other table metadata and fixed setup families still need migration.
The final full validation remains pending for implementation review.

### Binary output coverage projections

The three binary output coverage cases now use the complete native column-two
checks. The old per-case literal-size proofs are gone.
All eight original public theorem types pass the kernel preservation control.
The original definitions and imported values stay unchanged.
All three selected modules pass source checks and kernel replay. They include
both direct Shift consumers. Each replay uses the standard 32 MiB stack.
No safe dependency is skipped. These checks trust imported objects.
The source and replay batch takes 14.32 s and peaks at 848.71 MiB.
The binary row module builds in 2.23 s and replays in 1.81 s.
All eight focused axiom checks use only the three allowed axioms.
The four metadata controls and three generator controls pass.
The kernel rejects all four mutations. Generator and inventory freshness pass.
The inventory stays at 66,677 roots. Every established root remains.
Other table metadata and fixed setup families still need migration.
The final full validation remains pending for implementation review.

### Fixed Subword numeric source encoding

The numeric setup importer now handles fixed arrays with values above 255.
It uses the existing constant, arithmetic-run and append constructors.
The fallback applies where the old byte literal encoder rejected the input.
The old byte path keeps its output. Explicit packed-byte mode still rejects
values above 255. The code datatype and its soundness theorems stay unchanged.

Four exact kernel bindings cover actual fixed Subword source blocks. They
cover an arithmetic progression, wrapped values, a constant and a repeated
lookup. A closed normalization checker covers all four test requests.
The controls check that all four blocks stay before the program ROM regions.
The kernel rejects all four altered bindings.
A rebuilt rotation capture retains all 15 original encoded data values.
All 29 focused axiom checks use only the three allowed axioms.
All three selected modules pass source checks and kernel replay. Each replay
uses the standard 32 MiB stack. No safe dependency is skipped.
These checks trust imported objects.
The source and replay batch takes 20.91 s and peaks at 1030.58 MiB.
The final qualification takes 19.10 s and peaks at 821.11 MiB.
Both guards clean their owned workers. Inventory freshness passes.
The inventory has 66,691 roots. It retains all 66,677 established roots.

This closes the fixed Subword numeric encoding obligation.
The complete fixed Subword capture rollout remains open.
The final full validation remains pending for implementation review.

### Complete fixed Subword prefix captures

Four complete checks cover all 28 wholly fixed Subword source groups.
Columns 0, 1, 2 and 8 cover 5, 12, 6 and 5 groups.
Each column has one closed kernel result. It proves exact normalization and
the original row counts. The old fixed chunk facts are corollaries.
The part files retain all original data and all excluded program proofs.
The native assemblies import the complete fixed checks.
The scope excludes ROM halfword and byte tables. It also excludes every group
that crosses into either program region. Columns 3 through 7 stay unchanged.

All 877 original declarations remain. A kernel control accepts all 534 old
theorem types. All 343 imported data values are identical.
All 14 selected modules pass source checks and kernel replay. They include
the four native prefix assemblies. Each replay uses the standard 32 MiB stack.
No safe dependency is skipped. These checks trust imported objects.
The source and replay batch takes 86.25 s and peaks at 1402.66 MiB.
The final qualification takes 23.60 s and peaks at 825.35 MiB.
It also rebuilds the data-only column-one part with the default heartbeat limit.
The four complete captures use the default heartbeat limit.
Every guard cleans its owned workers.

All 1,033 focused axiom checks use only the three allowed axioms.
Four exact controls pass. The kernel rejects all four mutations.
Three generator controls check complete scope, retained program proofs and
untracked files. Capture and inventory freshness pass.
The source import graph has no cycle. Static checks and workflow syntax pass.
The inventory has 66,847 roots. It retains all 66,691 established roots.
The ten original module objects stay in `subword-fixed-original-oleans`
under the evidence directory.

Other fixed setup length and table metadata families still need migration.
The final full validation remains pending for implementation review.

### Complete fixed unified region-part lengths

Six complete checks cover 2,187 fixed region-part lengths in unified columns
2, 3, 4, 5, 6 and 7. Each column has one closed kernel result.
The new `PackedSetupLengths.check_sound` proves the original decoded lengths.
The checker computes numeric lengths. It does not decode stored values.
The views reuse the fixed equality trees and fixed special-span codes.
Fifty extra fixed pieces have exact source bindings.
The scope excludes the program ROM region. Its original proofs remain.
Scalar equality columns 0 and 9 stay outside this rollout.

All 20,137 original declarations remain. A kernel control accepts all 14,076
old theorem types. All 6,061 imported data values are identical.
All 32 selected modules pass source checks and kernel replay. They include
the six complete native prefix consumers. Each replay uses the standard
32 MiB stack. No safe dependency is skipped. These checks trust imported objects.
The pilot batch takes 151.41 s and peaks at 1720.79 MiB.
The remaining batch takes 342.70 s and peaks at 1683.71 MiB.
The final qualification takes 56.40 s and peaks at 1330.37 MiB.
Every guard cleans its owned workers.

The initial combined column-five replay exceeded the memory cap.
The adopted layout separates data, bindings, the certificate and projections.
It keeps one complete result per column. It adds no semantic proof shards.
All 26,775 focused axiom checks use only the three allowed axioms.
Five exact controls pass. The kernel rejects all five mutations.
Three generator controls check complete fixed scope, existing bindings and
untracked files. Capture, consumer and inventory freshness pass.
The source import graph has no cycle. Static checks and workflow syntax pass.
The inventory has 73,485 roots. It retains all 66,847 established roots.
The six original native module objects stay in `unified-lengths-original-oleans`
under the evidence directory.

Other fixed setup length and table families still need migration.
The final full validation remains pending for implementation review.

### Complete native seven-bit XOR table

One closed packed checker result covers all 386 native XOR7 blocks and
16,384 rows. The proved checker derives the original `output7` statement.
Sixteen bounded data bindings retain every original value and block boundary.
The data uses signed 16-bit word recipes. The checker uses packed arithmetic
and verifies the complete native sequence. The old literal splits are gone.
The old four-million-heartbeat override is gone.

The original public theorem type passes the kernel preservation control.
No imported data value changes. All six selected modules pass source checks
and kernel replay. They include both direct consumers. Each replay uses the
standard 32 MiB stack. No safe dependency is skipped.
These checks trust imported objects.
The checker batch takes 4.44 s and peaks at 808.62 MiB.
The capture batch takes 15.16 s and peaks at 897.20 MiB.
The consumer batch takes 12.93 s and peaks at 1006.95 MiB.
The final qualification takes 28.28 s and peaks at 1818.75 MiB.
All guards clean their owned workers.

All 106 focused axiom checks use only the three allowed axioms.
Five exact controls pass. The kernel rejects all five mutations.
They cover payloads, signed strides, domain bounds, the complete capture and
its source binding. Three generator controls pass. Freshness passes.
The inventory has 73,590 roots. It retains all 73,485 established roots.
Other fixed setup length and table families still need migration.
The final full validation remains pending for implementation review.

### Complete small native XOR checks

The native XOR3 and XOR4 certificates now each use one whole kernel result.
They use the existing Boolean `checkBlocks` checker and its proved soundness.
Their 64 and 256 rows pass with the default heartbeat limit.
The old literal splits and four-million-heartbeat override are gone.
Both original public theorem types pass the kernel preservation control.
No imported value changes.

The certificate and its direct consumer pass source checks and kernel replay.
Each replay uses the standard 32 MiB stack. No safe dependency is skipped.
These checks trust imported objects.
The certificate builds in 1.92 s and replays in 1.87 s.
The source and replay guard takes 4.35 s and peaks at 830.95 MiB.
The consumer and qualification guard takes 38.23 s and peaks at 1827.35 MiB.
Both guards clean their owned workers.
Both focused axiom checks use only the three allowed axioms.
Seven exact small-XOR and XOR7 controls pass.
The kernel rejects all seven mutations.
The inventory stays at 73,590 roots. Every established root remains.
Other fixed setup length and table families still need migration.
The final full validation remains pending for implementation review.

### Complete fixed edge-column lengths

Two closed kernel results cover all 71 fixed region pieces in unified columns
1 and 8. The column-one result reuses the fixed span and rotation bindings.
The column-eight result binds only fixed target pieces. Neither result includes
program ROM. The old program-region proofs remain.
The native prefix consumers derive their original length facts from these results.

All 437 original declarations remain. A kernel control accepts all 316 old
theorem types. All 121 imported data values are identical.
All ten selected modules pass source checks and kernel replay. They include
both complete native prefix consumers. Each replay uses the standard 32 MiB
stack. No safe dependency is skipped. These checks trust imported objects.
The source and replay guard takes 80.47 s and peaks at 1375.41 MiB.
The final qualification takes 44.28 s and peaks at 1325.02 MiB.
Both guards clean their owned workers.

All 680 focused axiom checks use only the three allowed axioms.
Nine exact controls pass. The kernel rejects all nine mutations.
Four generator controls pass. Capture and consumer freshness pass.
The inventory has 73,833 roots. It retains all 73,590 established roots.
Other fixed table metadata still needs migration.
The final full validation remains pending for implementation review.

### Complete fixed array samples

Three closed kernel results cover the store-placement template, both signed
byte-load templates and the byte-shift amount template. The checker verifies
all four 256-entry numeric arrays and their exact lengths.
Four kernel bindings connect the arrays to the original imported fields.
The original size and sample statements are corollaries of proved soundness.
The byte-template module now uses the default heartbeat limit.

All 16 original public declarations remain. A kernel control accepts all
13 old theorem types. All three imported data values are identical.
All 12 selected modules pass source checks and kernel replay. They include
both byte-load adapters, the fixed Subword rows and the Shift rows.
Each replay uses the standard 32 MiB stack. No safe dependency is skipped.
These checks trust imported objects.
The final wrapper and consumer batch takes 44.26 s and peaks at 1390.67 MiB.
The default-heartbeat control takes 4.21 s and peaks at 809.54 MiB.
The final qualification takes 48.85 s and peaks at 1439.71 MiB.
Eight exact controls pass. The kernel rejects all eight mutations.
All 43 focused axiom checks use only the three allowed axioms.
Three generator controls pass. Capture and inventory freshness pass.
The source import graph has no cycle. Static checks and workflow syntax pass.
The inventory has 73,860 roots. It retains all 73,833 established roots.

The initial whole-array comparison exceeded the memory cap. The adopted
checker traverses indexed samples. It separates numeric data from import
bindings. An explicit binding adapter avoids expensive simplifier conversion.
Every guard cleans its owned workers.
Other fixed setup lengths and table metadata still need migration.
The final full validation remains pending for implementation review.

### Complete fixed Subword region lengths

Nine closed kernel results cover all 45 fixed Subword region lengths.
Each capture includes the complete five fixed target regions for one column.
Exact bindings retain every original imported block and value.
The native prefix consumers project their original length statements.
The two program ROM regions keep their original proofs. Mixed source groups
in columns 3 through 7 remain outside the fixed normalization captures.

All 1,247 original declarations remain. A kernel control accepts all 869 old
theorem types. All 378 imported data values are identical.
All 45 selected modules pass source checks and kernel replay. They include
all nine complete native prefix consumers. Each replay uses the standard
32 MiB stack. No safe dependency is skipped. These checks trust imported objects.
The source and replay batch takes 200.93 s and peaks at 1015.04 MiB.
The final qualification takes 40.25 s and peaks at 814.46 MiB.
Both guards clean their owned workers.

All 1,409 focused axiom checks use only the three allowed axioms.
Six exact controls pass. The kernel rejects all six mutations.
Three generator controls pass. Capture, consumer and inventory freshness pass.
The source import graph has no cycle. Static checks and workflow syntax pass.
The inventory has 74,022 roots. It retains all 73,860 established roots.
Other fixed table samples and metadata still need migration.
The final full validation remains pending for implementation review.

### Complete aligned control and Shift samples

Two closed numeric results cover all 128 conditional-control samples and all
eight byte-shift position samples. Each result also checks every stored block
for constant values and 32,768-row alignment. Exact kernel bindings retain
all 47 conditional blocks and all four Shift blocks.
The proved getter and checker derive the original alignment and sample facts.

All six original public theorem types pass the kernel preservation control.
No imported value changes. All eight selected modules pass source checks and
kernel replay. They include both direct pair-row and Shift-row consumers.
Each replay uses the standard 32 MiB stack. No safe dependency is skipped.
These checks trust imported objects.
The source and replay batch takes 48.07 s and peaks at 1074.67 MiB.
The final qualification takes 32.40 s and peaks at 797.20 MiB.
Both guards clean their owned workers.
Eight exact controls pass. The kernel rejects all eight mutations.
All 28 focused axiom checks use only the three allowed axioms.
Three generator controls pass. Capture and inventory freshness pass.
The source import graph has no cycle. Static checks and workflow syntax pass.
The inventory has 74,044 roots. It retains all 74,022 established roots.

The wider per-capture rollout remains open. Query-frame import still emits
one closed check for each field and joins proof shards. This family needs a
complete numeric checker. Other generated frame and argument families also
need a scope audit. Fixed source-shape bindings and generic semantic case
proofs stay distinct from per-capture numeric checks.
The final full validation remains pending for implementation review.

### Complete AddSub query-frame pilot

Both AddSub captures now use one closed numeric query-frame result.
The checker verifies every erasure exclusion, bank-address round trip and
exact polynomial transport. It retains constant terms and their full order.
Its proved soundness derives the original typed Boolean predicate.
The original semantic finalizer stays in place. Every old per-field check is
a corollary of the complete result. Both captures use default heartbeats.

The capture command materializes closed natural data before the Boolean check.
It accepts only natural literals and numeric constructors. A separate kernel
equality binds the complete capture to the original fields, coordinates,
placements and bank addresses. The original imported values stay unchanged.

All 42 original declarations remain. A kernel control accepts all 36 old
theorem types. All six imported data values are identical.
All 15 selected modules pass source checks and kernel replay. They include
both direct materialized-witness consumers. Each replay uses the standard
32 MiB stack. No safe dependency is skipped. These checks trust imported objects.
The checker source and replay guard takes 7.35 s and peaks at 827.43 MiB.
The capture guard takes 43.63 s and peaks at 878.49 MiB.
The finalizer guard takes 15.25 s and peaks at 829.90 MiB.
The consumer and qualification guard takes 61.26 s and peaks at 834.07 MiB.
All guards clean their owned workers.

All 63 focused axiom checks use only the three allowed axioms.
Nine exact controls pass. The kernel rejects all nine mutations.
The legacy importer path passes. The importer rejects opaque numeric payloads.
Three generator controls pass. Capture, interface and inventory freshness pass.
The source import graph has no cycle. Static checks and workflow syntax pass.
The inventory has 74,065 roots. It retains all 74,044 established roots.
This small pilot qualifies the binding and semantic transport. It does not
establish a timing gain for the query-frame family. The other 20 captures
and the larger-capture measurements remain open. Other generated frame and
argument families also need a scope audit.
The final full validation remains pending for implementation review.

### Query-frame scaling probe

The unadopted BlakeRound probe contains all 1,152 fields.
Its closed numeric payload builds in 44.76 s and replays in 1.96 s.
Materialization needs a bounded recursion depth of 8,192 and a scoped
2,000,000-heartbeat limit. Replay still uses the standard 32 MiB stack.
The complete source-record binding exceeds the 2,560 MiB footprint cap.
The guard stops it at 2566.85 MiB and cleans its owned workers.
The complete result and preservation controls do not run after that stop.

A direct coordinate binding passes source and replay checks. Its guard takes
4.84 s and peaks at 892.42 MiB. A combined metadata and edge-field binding
probe also exceeds the cap. Its buffered messages do not identify the first
expensive binding. Isolate each component before the next probe. Use bounded
exact binding leaves for the expensive lists. Keep one complete Boolean result.
All scaling sources stay in the evidence directory. No large capture is adopted.
The other 20 query-frame captures remain open.

## Rebase checks

The branch now uses base `c1a662222cafcd96db4383dce737edb79fa62b09` from
`origin/av_gkr_compiler`. The remote tip matched this commit on 29 October 2026.
The local EVM initialization-window fix is present.

The three target definitions passed a focused source check. That check used
the retained dependency cache. It does not validate the changed native imports.
The native setup exporter passed its scoped Cargo check and build. All 16
setup exports and all 22 compiler captures regenerated. The setup artifact and
native evidence checks passed. The padding regression passed after removal of
the redundant full-domain CPU cache. The retained lock adds only the local
cs-to-prover edge required by the new base. It changes no package version.
Setup freshness passed. All 12 native generators ran. All 16 fresh setup JSONs
matched. Native dep-info covered 551 inputs. The refreshed manifest covers 731
source files.

The compiler and lookup provenance checks passed after regeneration. The
unified table and decoder setup scaffold checks also passed. The decoder
oracle rebuilt with the current sources on Lean 4.31.0.

The changed unified, bigint and initialization imports passed focused builds.
The four changed split imports passed in both cache modes. The split group
clock, derived-borrow, control-bound, physical-port and memory-order proofs
passed kernel elaboration on the new layouts. The split import test module
also built. All 22 production-program decoder comparisons passed in both cache
modes with the current oracle. All 68 small-program comparisons also passed.
These cover both cache modes for two ordinary programs, an extended-round
caller and the blessed split Keccak caller. The small matrix used an optimized
exporter build. It changed no Rust source or dependency version.
The compiler binding builds passed. The bigint and unified wiring
certificates passed in both cache modes with fresh native graph imports.
The wiring generator check passed for all 22 captures and 304 module targets.
The full arithmetic and windowed agreement generator checks also passed.
All four current arithmetic imports passed focused checks. The complete
compiler group passed 497 checks. It covers every bigint and unified compiler
case module, both cache modes, the shared logical and program execution
consumers, and the decoder dependencies that those consumers import.
The group reuses the unchanged finite-table cache. Earlier batches reached
their time limit or found stale cache imports. The last batch passed and left
no owned process running. All checked module records remain available.
The windowed witness and public-boundary templates now use the imported input
list length. They no longer fix the old 145-wire dimension. The public-table
tag proof uses the new ROM gate and pooled query columns. Its statement and
premises stay the same. All eleven final source and generator checks passed.
Earlier build results apply to the old base.
Unified's current column-role inventory, dispatch bound and ordinary PC
increment passed focused kernel builds. Bigint's current column-role inventory,
control-bit proof and timestamp proof passed. Bigint's additive, equality and
multiplication writeback proofs passed on the derived EQ selector equations.
Bigint's memory rules, address soundness and memory value bounds passed
focused checks with the current timestamp columns.
Unified's control projection, control lookup resolution and jump arithmetic
passed focused checks on the new shared columns and affine write gates.
Unified's zero-register preservation and timestamp proofs passed focused
checks. The pooled ROM memory-port adapter also passed with the current
timestamp record. These close the native zero-write and clock obligations
used by the machine targets.
Unified's memory, ROM, binary, shift, TRIADD, XOR/rotate and modular proofs
passed focused checks. Its existing native caller-path proof also passed.
These restore the native instruction obligations on the new layout.
The combined stream target still needs its execution proof.
Its initialization adapter passed a focused kernel check. The adapter binds
the public text registry and native seed to the combined stream boot inputs.
Its two proofs use only the three allowed axioms.
Unified's native external-read specification and register-history execution
proof passed focused kernel checks. They keep the stream slot binding
explicit. Both proofs use only the three allowed axioms. Stream ordering and
the combined execution proof remain open.
The external-hint specification and exact register-history execution also
passed. Public text supplies aligned, bounded instruction PCs. Public setup
and initialization supply all ordinary execution inputs. The combined registry supplies native x0 rules for
ordinary, modular, external and worker rows. These proofs passed focused
kernel checks. Their axioms stay within the three allowed axioms. Exact
request and RAM matching remain explicit.
Native prefixes retain the same stream slots and public memory inputs.
The combined registry now supplies one machine and worker memory history.
This conditional history keeps the round-mask contract explicit.
Indexed cut composition carries the stream position through each cycle.
These proofs passed focused kernel and axiom checks.
External and modular instructions now retire in the actual shared cycle
history. Their cycle proofs passed focused kernel and axiom checks.
Ordinary arithmetic, TRIADD and XOR/rotate now retire in the stream registry's
shared native history. Their adapters passed focused kernel and axiom checks.
Control, comparison, binary, shift and RAM cycle adapters also passed focused
kernel and axiom checks. All instruction classes now have native cycle proofs
for the combined registry. The native read bit matches public metadata.
Ordinary, custom, modular and caller rows consume no stream words. These
selector proofs passed focused kernel and axiom checks.
The combined noncaller dispatcher also passed. It selects the public Sail
clause for every ordinary, custom, modular and external-input row. It proves
retirement in the actual native cycle and the exact stream-count change.
The current dispatcher uses the existing physical RAM profile. The native ROM
adapter must remove that intermediate restriction before it closes Unified.
Native clocks now prove the zero initial stream count, each cycle's exact
increment, and the total terminal count. These proofs passed focused kernel
and axiom checks. They add no ordering premise.
Indexed path composition now proves the combined execution from exact native
cycle facts. It includes the final PC, terminal memory and stream count.
Its kernel and axiom checks passed. This theorem retains native caller-cycle
facts and the physical code profile as explicit inputs.
The native caller adapters also passed focused kernel and axiom checks.
The conditional native stream entrypoint derives all caller cycles from
current worker equations and the shared history. It retains explicit bigint
commands, hash-controller contracts and the physical code profile.
The stream-aware prefix induction now derives those worker controls from
public supported use. It proves combined execution under the intermediate
physical RAM profile. Its kernel and axiom checks passed. Private command and
controller contracts are conclusions at this entrypoint.
The joint worker-control and worker-domain induction passed kernel checks.
It derives both contracts from public supported use and exact native prefixes.
Native prefix cutting now uses seed clock bounds. It does not equate native
zero ROM values to physical program bytes. The ROM input and terminal adapters
also passed. The native supported-path theorem now proves combined execution
with the original native terminal view. All checked roots use only the three
allowed axioms. The public decoder and acceptance adapter also passed.
The final `unified_soundness : Unified` theorem passed a focused kernel check.
Its axiom report lists only `propext`, `Classical.choice` and `Quot.sound`.
The check used the retained dependency cache. Full environment auditing and
transitive kernel replay remain pending. All 12,457 pre-rebase audit roots
remain in the explicit inventory. The reduced target proof is now also complete.
Its public ordinary and caller images and standalone initialization adapter
passed focused kernel and axiom checks. Its shared stream/caller memory theorem
also passed. Native matching derives clocks, zero-register reads, canonical
word bounds, worker operations and one actual Sail memory history. The round
controller contract remains explicit at this intermediate memory interface.
The public supported-use proof now derives this contract.
Reduced arithmetic, modular, external, shift, bitwise and control-flow clauses
now have shared-history execution adapters. Their focused kernel and axiom
checks passed. These adapters take actual operands and histories from the shared
transport. The control adapter keeps its native final-PC range explicit.
The native PC path now derives that range from state matching and the typed boundary.
The reduced LW/SW address, native transport and full instruction adapters
also passed focused kernel checks. They use shared initialized address codes
and readonly-ROM history. The native clock proofs derive unique aligned row
clocks, four-tick advancement and exact CPU event windows. Their axiom reports
use only the three allowed axioms. Global cycle and caller composition now pass.
Exact caller slots now identify every worker in each native instruction
window. The cycle split and ordinary row history passed focused kernel checks.
State matching and the existing typed boundary derive every final-PC range.
Native clocks derive the initial, per-cycle and terminal stream counts.
Their axiom reports use only the three allowed axioms. The ordinary dispatcher,
complete caller retirement and supported-use composition now pass.
The reduced ordinary dispatcher has now passed focused kernel and axiom checks.
It binds all four native CPU families to the public modular/external clauses,
actual shared cycle states and exact stream increments. The native ROM adapter
now supplies its readonly-event property. Caller retirement and supported-use
composition now pass.
The complete reduced caller-cycle adapter has now passed focused kernel and
axiom checks. Exact slots select one actual worker. Shared history supplies
its reads and frame. The extended-round reference and native caller PC equations
prove complete retirement. The full CSR query disables external reads on callers.
Round control, worker RAM binding and readonly-ROM history remain explicit at
this intermediate interface. The native prefix induction now derives them.
The complete reduced native path now composes those ordinary and caller cycles.
It proves `ReducedRealizes` with final PC, shared terminal memory and exact
stream consumption. Its focused kernel and axiom checks passed. Native worker
liveness places every worker event inside the same path. Seed-clock lemmas
also support raw native prefixes without equating ROM bytes to native zero.
Native ROM transport, joint supported-use induction and public decoder
acceptance assembly now complete the reduced target.
The ROM-aware code-frame lemmas passed focused kernel and axiom checks.
Interpreted ROM events refresh the same public word. Fetch transport can use
that readonly history without the global tracked-RAM lower bound. The worker
RAM binding remains explicit at this intermediate transport interface.
The full ROM-aware native path passed focused kernel and axiom checks.
It includes load/store retirement, caller retirement, and final stream count.
The public setup and initialization supply its ROM execution profile.
Worker ABI bounds now follow from each exact worker-port binding.
These results admit tracked low ROM cells. No global tracked-RAM lower bound
occurs in this path. The joint prefix induction must derive worker-port
binding from the public runtime argument contract. That induction has now
passed focused kernel and axiom checks.
The ROM-aware load/store cycle proof also passed. It uses the current native
equations for readonly loads. It removes the global RAM lower bound from this
cycle proof. A separate worker-port lemma derives each indirect RAM bound
from exact worker-domain binding. The public ROM profile admits low ROM
shadow cells. The joint worker-domain induction and final Unified target
assembly now pass.
All nine ordinary worker and CPU memory-port inventories passed focused
checks. Their timestamp records use an explicit absent borrow subtrahend.
The focused circuit and proof group passed all 288 module checks.
This group includes the timestamp tests, native path and span execution,
supported delegation use and the three target propositions.
An earlier batch hit its resident-memory cap
while it rebuilt an unchanged extended-round import. That was a resource stop.
The later batches used the documented 5,120 MiB resident cap.

The normal dependency build reached its 1,800-second limit while it rebuilt
unchanged shift certificates. The guard left no owned process running.
The focused checks now use a separate object directory. A declaration
dependency inspection found no use of the changed timestamp-group record or
bigint range input in the 64 retained shift certificates. The focused checks
reuse this mathematical cache. This is not a full frontend build or kernel
replay of all dependencies.

Lake now tracks all six split circuit JSONs and all three split setup JSONs.
These inputs serve the full unsigned target's three fixed-setup premises.
The provenance controls check that Lake requires each native JSON input.
All 20 controls passed. A focused build passed with the new dependencies.

The focused rebase qualification passed. The full frontend build, environment
audit and baseline refresh, transitive kernel replay, and Linux runtime and
warm-cache qualification did not run. They remain pending for user review.

The full unsigned relation now combines the six CPU families, modular MOPs,
nondeterminism reads, bigint, BLAKE2 extended-round and the three split Keccak
calls in one stream execution. Its caller registries are functions of public
text, with a proved generic public-byte/source lemma and inclusion of the
existing ordinary/caller steps. The new split micro-call reference uses the
blessed control schedule, the inverse-Pi physical slot map and the existing
Keccak round constants. Kernel checks establish distinct touched slots for all
361 calls and the final round's identity slot map. Native worker-to-reference
soundness, complete 361-call functional composition and registry disjointness
remain open; these reference checks do not establish native circuit coverage.

The split-worker native interface now selects all six exact compiled
constraint/lookup/timestamp imports, invocation columns and memory ports by
worker kind and cache mode. It states participation and exact memory-token
matching as explicit logical acceptance premises. Setup provenance, grouped
memory effects, complete split caller composition and functional soundness remain
open. A separate split request interface retains full-width CSR addresses and
exact virtual-token matching for the three blessed worker families; focused
proofs derive one-to-one nonzero fulfillment and bounded invocation clocks
from machine constraints and the public initial clock. Exact decoder matching
and public Sail bytes also fix each matched worker's split kind. The imported
ADD/SUB constraints prove canonical caller PC retirement. Shared caller/worker
memory composition and functional worker soundness remain open. A focused split
memory proof now derives bounded timestamps for all physical reads and writes
from public seed clocks, caller-derived worker clocks and the explicit RAM
permutation. A generic grouped-clock lemma proves strict read-before-write order
from a positive compiled read distance. All four theta/rho and six chi5 groups
have exact clock equations and Boolean borrows extracted from both cache modes.
Both column-parity captures additionally derive every per-port Boolean borrow
and timestamp comparison bound directly from their imported equations and
lookup queries, then prove strict read-before-write order given the public
invocation and logically matched previous-clock bounds.
For theta/rho and chi5, an explicit public controller-table soundness premise
now yields one-hot iteration flags or a bounded row index. The complete
uncached split setup exports are retained and provenance-checked; cached and
uncached exports have identical fixed columns and table metadata. The imported
controller regions have kernel-checked row properties and genuine static-table
soundness theorems. Proving that every active tagged lookup in the full generic
setup belongs to these regions remains open. The complete theta/rho generic
table is now imported, and a kernel-checked structural proof isolates its
controller tag to the exact retained 121-row region. Row equality between the
generic view and the sliced view, and the corresponding chi5 result, remain
open. Native fixed-table lookups then
give positive, nonwrapping distances and strict order for all groups in both
cache modes. Complete memory effects remain open. All theta/rho and chi5 physical ports now
have kernel-checked group ownership in both cache modes. A common theorem proves
strict read-before-write order for all six capture families. Exact RAM matching,
public initial clock bounds and the explicit controller premise now yield the
complete split-pool logical RAM history facts: matching, preserved addresses
and strict per-port time order. Functional worker effects remain open.

Both cached and uncached native captures remain required. The checker migration
must qualify all 22 capture configurations.

The adopted AND checker and its measurements appear above. The earlier packed
OR, XOR and unified XOR8 pilots remain available. Their production Block and
setup-prefix facts still need migration. The setup-column pilot is proved and adopted for column 2.

## Supporting proved results

| Area | Result and scope |
| --- | --- |
| [Ordinary circuits](Airbender/Review/Circuits/README.md) | Arithmetic, branches/jumps, comparisons, shifts/bitwise and word/subword memory have reference soundness proofs. Local public-image histories and native ROM-shadow histories are distinct interfaces. |
| [Whole execution](Airbender/Review/Trace/README.md) | Pooled and unified source/trace execution bind final PC and every tracked cell, including registers, for programs admitted by their selected registry. Branches and repeated-PC loops are supported. Discarded x0 writes missing from a registry remain outside it. |
| [Unified stream inclusion](Airbender/Proofs/UnifiedReduced/FullStreamInclusion.lean) | Every existing mixed ordinary/custom or complete delegated-call step lifts to the stream-aware unified relation without consuming a stream word. Finite runs lift, and existing no-read whole-execution results retain their terminal claims when the native read count is zero. The complete `Unified` target now proves native soundness of this combined relation from its explicit public and exact-matching premises. |
| [Delegated workers](Airbender/Review/Trace/Workers/README.md) | Bigint, BLAKE2 and special5 Keccak compose under explicit call contracts. Complete algorithms require protocol coverage and valid memory gaps. Extended-round masks remain witness premises in lower-level integrated APIs as well as worker APIs. |
| [Supported delegation use](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean) | Public wrapper shapes, safe entry and reference-prefix validity derive bigint/G/extended-round worker contracts. G pointer separation remains in the public domain; accepted complete G spans also derive separation from memory matching. Public initialization, tracked RAM, configuration, setup and exact matching remain explicit. |
| [Provided Keccak wrapper](Airbender/Review/Compiler/MachineTargets.lean) | Proved in the full unsigned target. The target includes the blessed 361-call split sequence under its stated supported-use and exact-matching premises. The 649-call special5 protocol stays separate. Special5 calls remain excluded from the target. |
| [Initialization](Airbender/Review/Trace/Initialization.lean) | Native standalone/inline adapters derive seeds for ordinary pooled/unified execution. External-read, modular, TRIADD/XORROT and delegation extensions retain their own seed premises. |
| [Reduced public program](Airbender/Proofs/Trace/ReducedPublicProgram.lean) | The public reduced decoder filter is definitionally the stream-aware reduced filter. Every projected ordinary entry uses one of its four native CPU families, so the reduced-run inclusion no longer needs a separate family premise for text-derived programs. Every projected virtual caller is the BLAKE2 extended-round CSR; the special5 exclusion follows for reduced text. This does not establish native decoder setup binding or whole-machine soundness. |
| [Public program setup](Airbender/Review/Compiler/PublicProgramSetup.lean) | New unrolled and unified interfaces bind independently supplied decoder columns, the actual imported circuit masks, capacity, delegation group syntax and initial image to public text. [The imported mask constructors](Airbender/Proofs/GKRProtocol/ProgramMasks.lean) satisfy that binding. [Source and classification theorems](Airbender/Proofs/GKRProtocol/PublicProgramCases.lean) map a range-checked query in those columns to a Sail-sourced ordinary instruction or virtual caller in its corresponding public program. [Native row corollaries](Airbender/Proofs/GKRProtocol/PublicNativeRows.lean) use an explicit exact decoder lookup premise to classify actual trace rows; [accepted-row corollaries](Airbender/Proofs/GKRProtocol/PublicAcceptedRows.lean) derive the required PC range from constraints, state matching and the public initial PC. Matching each compiled circuit's lookup to the supplied columns, deriving native acceptance from all certificates, then proving compiler execution remain open. |
| [Compiler preservation](Airbender/Review/Compiler/README.md) | Base-field arithmetic preservation covers 22 captures. Fourteen row compositions derive helper bounds, authored lookup membership and source validity from physical native arithmetic/active rows and exact emitted-tuple matching. Separate public-text row models have generic active-PC membership for ordinary instructions and full-width delegation-CSR caller rows, with captured masks and ROM capacity. A range-checked active modeled decoder row, including its selected native column mask, now yields an ordinary or virtual caller entry sourced from public Sail bytes. Caller source includes the decoded CSR shape and configuration allowlist; an effectful decoder result is not silently accepted. A generic initial-ROM lemma places each present public text word into the modeled word-ROM table. The caller projection also requires a public well-formed call-group premise to match native preprocessing. The compiler wrappers still require retained four-entry tables; the differential checks do not yet replace that premise. |

Upstream #531 merged as `06c15f275` and is in the new base. The unified
base-layer entrypoint now returns the verified registers. It no longer returns
the fixed success vector. New-base runtime validation remains pending.
See [the source](../../tools/gkr_verifier/src/common_fsv_unified_base_sec_100.rs)
and the [trust boundaries](TRUST_AND_REVIEW.md).

Exact natural-multiplicity lookup matching, state/RAM permutations and public
boundaries remain assumptions. Sampled sum/product equality does not establish
those exact relations. Cryptographic argument soundness, universal Rust compiler
correctness, import/generation fidelity and completeness are outside these claims.
The [supported-use domain](Airbender/Review/Trace/UnifiedReduced/DelegationUse.lean)
excludes invalid bigint/hash invocations and special5 calls. Its round rule is the
blessed mask with zero low limb; arbitrary VM calls have a wider domain.

## Validation evidence

This table is the maintained evidence inventory. Historical counts and detailed
receipts belong in [verification checkpoints](VERIFICATION_HISTORY.md), rather
than repeated in the guides. Changes after a checkpoint require their own checks.

| Gate | Last completed evidence / outstanding work |
| --- | --- |
| Repair controls | Mac: 68 policy/provenance/generation tests pass; 26 guard tests pass and four Linux-only tests skip; 23 pool policy/process tests pass. All six affected generator roundtrips, 14 complete lookup bindings and the independent export-byte validator pass their focused checks. These are not a complete frontend or Linux-backend qualification. |
| Reference known answers | The XKCP all-zero permutation regression passes a normal Lean build (14.39 seconds, footprint 927.56 MiB, resident 3251.11 MiB). The NIST FIPS 202 SHA3-256 empty-message permutation vector passes a focused guarded build at the current source. RFC 7693 abc and all 14 lookup bindings elaborate against cached imports; they still require the complete dependency rebuild below. All guarded focused jobs leave no surviving workers. |
| Split Keccak imports | All six worker constraint imports and both cache modes passed focused checks on the current base. The derived-borrow, clock, control and memory-order proofs also pass. The full unsigned target proves the blessed sequence under its stated supported-use and exact-matching premises. Final frontend and transitive replay remain pending. |
| Setup provenance | All 16 setup artifacts and all 22 compiler captures regenerated for the current base. Setup identity, source hashes, freshness, padding and decoder comparisons passed. Fresh reconstruction covered 551 native dep-info inputs and the manifest covers 731 source files. See the rebase checks above. |
| Public-text decoder row model | Native public-program adapters cover all 14 CPU profiles. They bind native constraints, caller metadata, decoder queries and ROM/PC facts to independently supplied public text. Exact lookup and RAM matching stay explicit. The stateful Sail decoder theorem preserves the public initial state. The canonical acceptance graph excludes captured decoder-tail and retained-image contracts. Compatibility APIs keep their original declarations. The final environment audit remains pending. |
| Packed checker pilot | The original AND Block statement now follows from one kernel-checked packed certificate and its proved soundness theorem. The native setup consumers pass focused checks. See [the measurements and cache trust](#verified-checker-measurements). The setup-column pilot is adopted for column 2. Broader rollout and cold full measurements remain open. |
| Decoder differential | The state-aware oracle matches all 14 applicable public OS comparisons in both cache modes. The MUL/DIV regression and all 22 committed-verifier comparisons pass in both modes. Earlier small-program matrices cover ordinary instructions, BLAKE2 callers and the blessed split caller. The focused oracle relink trusts retained dependency objects. Normal executable dependency freshness remains pending. These checks prove decoder agreement for the tested programs. They do not prove OS execution. |
| Reduced setup export tooling | The exporter accepts `--reduced` for the four shared unrolled CPU families. `cargo check --locked -p execution_prover --example export_setup_json` and the source-pinned manifest check pass. The executable build succeeded with `CARGO_PROFILE_DEV_DEBUG=0`, avoiding the local LLVM DWARF SIGBUS; focused native exports then completed. |
| Complete source/runtime/review frontend | Passed on Mac at f0b059fe6412: 4,862 modules, 219 concrete Tests, five retained Sail modules, 3,509 runtime native modules, library and both executables. Normal Lake freshness, artifact hashes, direct axiom comparison, importer runtime and review checks passed. The 23 guarded jobs took 260.14 seconds from a normally built cache; peak footprint 855.31 MiB and resident 4279.14 MiB; no surviving workers. This is historical evidence for the source before the Review reorganization. |
| Linux native setup freshness | Passed at ac90532c92b1: 12 generators, 13 complete exports, receipts and 546 dep-info inputs; 242.97 seconds, peak charged memory 1629.62 MiB, no surviving workers. |
| Native compiler capture reproduction | Passed at ac90532c92b1: all 67 root files reproduced byte for byte, with retained/fresh validators and provenance controls. Derived interpretation/lookup directories have separate validators. |
| Linux process controls | Passed at ac90532c92b1 on aarch64 Linux: 29 guard and 23 pool tests. The subsequent exit-race repair requires fresh runtime controls. |
| Complete Linux frontend / cold reproduction | The cold attempt stopped after 3,883 completed source-build steps when Docker became unavailable; launcher exit 255, interrupted leaf has no result. No complete Linux frontend or cold pass was issued. Preserve that partial cache as recovery data, not passing evidence. |
| Whole-environment axiom audit | Pending. The Mac attempt stopped after 125.97 seconds at resident 5125.94 MiB against the unchanged 5120 MiB cap (footprint 1193.53 MiB); no surviving workers and no successful audit result. The IotaMapping dependency discrepancy has a reviewed disposition, not a regenerated passing baseline. |
| Independent transitive replay / negative controls | Pending. Earlier selected-module replay did not replay imports transitively. The 32 MiB stack remains provisional until the deep modules and full dependency graph pass. |
| CI qualification | Advisory. Current cold/warm runtime, cache sizes and complete replay feasibility on the configured runner are not established. Its 22-hour shared work deadline and 24-hour job boundary do not establish feasibility. |

The allowed standard axioms are propext, Classical.choice and Quot.sound. All
12,409 established explicit audit roots remain required; additional definitions
may add roots. Baseline updates must come from a successful environment audit
with reviewed deltas. A direct report is a smoke check, not that audit.

## Remaining milestones

1. Validate the assurance repairs and conservative Review reorganization without
   dropping public declarations, audit roots, imported values or assumptions.
2. Finish whole-environment auditing, independent transitive replay and isolated
   false-proof controls; measure Linux cold/warm and CI feasibility.
3. Convert measured per-capture fact families to once-proved Boolean checkers,
   then qualify build and replay cost. Cryptographic soundness, universal Rust
   compiler correctness and completeness remain in the
   [deferred milestone register](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

[Reproduction](README.md#reproduce) gives commands and resource limits.
[Findings](FINDINGS.md) distinguishes supported-use exclusions, conditional proof
coverage and implementation issues. Production circuits are not changed to make
proofs succeed; discrepancies require documentation and narrow explicit assumptions.

### Reduced native ROM obligation

The reduced native ROM adapter passed its focused kernel check. It derives
canonical addresses from exact shared matching and strict native clock order.
It does not assume physical values in the native zero seed. ROM interpretation
preserves imported constraints, decoder queries, callers, requests and shared
memory matching. It preserves public instruction bytes and external responses.
The physical initialization adapter and complete conditional reduced path pass.
Worker controls and RAM port locations remain explicit intermediate premises.
The public supported-use adapter now proves them. Public decoder acceptance
also passes. The final reduced machine target is proved.

The check used Lean 4.31.0 and retained unchanged dependency objects. All selected
roots use only the three allowed axioms. The full frontend, environment audit,
transitive kernel replay and Linux qualification did not run.

### Reduced public supported-use obligation

The reduced prefix and supported-use proofs passed focused kernel checks.
Each prefix keeps exact request and RAM matching. Its actual caller endpoint
supplies a typed verifier boundary. Joint induction proves native round controls
and each worker port location from reachable public reference arguments.
The native path now has no private worker-control or port-domain premise.
The public decoder and native acceptance adapter now pass. The final reduced
target is proved. Full validation remains pending as stated above.

### Reduced target proved

`MachineTargets.Proofs.unrolled_reduced_soundness` proves the unchanged
`UnrolledReduced` proposition. Public text and the actual imported masks supply
full decoder queries. The proof derives the omitted funct3 field where needed.
Native selectors classify ordinary and caller rows. Exact state matching bounds
the incoming PC without a separate CPU RAM permutation. The proof connects
standalone initialization and public supported use to the full reduced path.
No private worker control or port-domain premise remains in the final theorem.

The focused source and axiom check passed on Lean 4.31.0. Its selected roots use
only `propext`, `Classical.choice` and `Quot.sound`. It retains unchanged finite
table objects. It is not a full frontend or transitive replay. The environment
audit and Linux qualification remain pending. Work now resumes the full unsigned
machine and the blessed split Keccak sequence. The packed checker pilot stays
at its current scope until all three machine targets are done.

### Full unsigned initialization obligation

The full unsigned standalone initialization adapter passed a focused kernel
check. Public text constructs the six-family ordinary stream image and the
separate standard and split caller images. The standard filter retains exact
bigint and extended-round decoder metadata. The adapter derives boot inputs
from the unchanged standalone initialization boundary, public profile and setup.
The full unsigned machine target remains open. Its native combined path and
blessed split Keccak function are not yet proved. Full validation remains pending.

### Split native worker coverage obligation

The native invocation proof passed for all three split worker kinds and both
cache modes. An active worker cannot use invocation zero. The proof uses the
actual imported initial timestamp lookup. It adds no schedule or positive-clock
premise. Exact request matching can therefore account for every active worker.
The complete full unsigned execution proof remains open.

### Split generic controller binding obligation

The complete theta/rho and chi5 imports now supply their controller facts.
The row proofs select the exact controller regions from the native field tags.
The imports keep every physical column. They retain padding inside the
generic table extent. They omit the physical padding after that extent.
The proofs use certified block lengths to skip the large table prefixes. The runtime regression compares every parsed theta/rho block and value.
It also checks the complete table extent and native region data. A kernel
proof checks the exact source bytes. All checks passed. The fifteen new
audit roots use only the three allowed axioms. All old roots remain present.
The explicit inventory now contains 12,714 roots.

The source-to-data bridge in `FixedSetup` remains open. Its JSON parser has an
opaque kernel worker. The imported table proofs do not close this bridge.
The split worker functions and the complete blessed sequence also remain open.
Full validation remains pending.

### Split exact worker-accounting obligation

Exact native request matching now accounts for every active split worker.
The proof removes the zero-clock exception with the native liveness theorem.
Every worker has an actual caller with the same full-width CSR and timestamp.
Both new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,716 roots. All prior
roots remain present. No function or complete execution claim follows yet.

### Full unsigned public decoder obligation

Exact public lookup now classifies every actual row of all six CPU families.
The proof restores the unused funct3 slots from public instruction metadata.
Native selectors separate ordinary rows from standard and split callers.
All five admitted caller forms retain the original public Sail source and
complete CSR query. The public special5 exclusion stays explicit.

Six new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The inventory now contains 12,722 roots. All prior roots remain
present. This closes the target's public row-classification obligation.
The combined native execution and remaining split obligations stay open.

### Full unsigned split request-channel obligation

The full target's combined request permutation now supplies the split channel.
Filtering uses the complete CSR address. Standard worker requests cannot enter
this channel. Public decoder lookup supplies the split caller registry.
The public text image and initial PC boundary supply its input conditions.
Every active split worker has an actual caller with the same CSR and raw clock.
The proof adds no request-matching or witness-schedule premise.

Six new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,728 roots. All previous
roots remain present. Split functional effects, supported-use execution and
the setup-source bridge remain open. Full validation remains pending.

### Blessed split reference-composition obligation

The original split reference now produces the original Keccak permutation.
The proof composes all 361 calls. It checks all 24 parity, theta/rho and chi
phases. It includes the final delayed iota and the return to the original
physical lane layout. A kernel proof checks the finite index cache. The cache
changes no operation, reference or public theorem statement.

All 41 new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,769 roots. All
previous roots remain present. The last bounded group passed. It left no owned
process running. Earlier attempts found reduction limits or reached the memory
cap. Smaller proof units passed under the unchanged resource limits.

Native split circuit soundness remains open. The next obligations are the
fixed-table arithmetic facts, each worker's actual functional read/write
effect, and the combined native history with supported-use induction. The
`FixedSetup` source bridge also remains open. The full unsigned target and
final lengthy validation remain pending.

### Native chi5 lookup arithmetic obligation

The retained chi5 generic table now proves exact nibble arithmetic.
A tagged native lookup derives all five input bounds and output bounds.
Each actual output equals chi of its actual cyclic input fields. The proofs
cover every arithmetic row. They add no operand or expected-result premise.

The importer stores small shared literal leaves for the large native prefix.
It checks every parsed value before it emits the index view. The full-column
runtime regression passed after emission. It compares every value, including
physical padding. The controller proofs also passed with this representation.
The input bindings, output bindings and arithmetic identities use kernel proofs.
The final focused checks list only the three allowed axioms for all 29 new roots.
The explicit inventory now contains 12,798 roots. All prior roots remain present.

Native worker retirement and combined memory execution remain open. The
`FixedSetup` source bridge remains open. Full validation remains pending.

### Native chi5 arithmetic-query obligation

Both compiled cache modes now derive all sixteen arithmetic lookup results.
The proof uses their actual imported query entries and retained generic table.
It derives input bounds, output bounds and the exact cyclic chi operation.
The native constant tags need no execute or operand premise at this layer.

Eight new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,806 roots. All
previous roots remain present. Lane packing, worker retirement and combined
memory execution remain open. Full validation remains pending.

### Native chi5 lane-effect obligation

Both native cache modes now prove the complete chi effect on actual memory
lanes. The proof binds each native read and write limb to its four arithmetic
queries. All 80 packing cases passed kernel checks. Lookup bounds recover each
canonical sixteen-bit limb. Bitwise assembly proves the sixty-four-bit lane
operation. The proof adds no operand or expected-output premise.

Twelve new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,818 roots. All
previous roots remain present. The final bounded group passed and left no owned
process running. Native control and memory retirement remain open. The fixed
setup source bridge and the full unsigned target remain open. Full validation
remains pending.

### Native chi5 control and memory-effect obligation

The actual chi5 controller lookup now selects the original blessed call.
The proof binds its control transition and all five physical slots. Native
constraints force both control-register high limbs to zero. Exact token codes
retain these values. Port enumeration covers both registers and every lane
half. Both pointer limbs stay explicit in every raw RAM address.

The native outputs equal the original split reference result. These facts hold
for both cache modes. They add no operand, schedule or expected-output premise.
They do not yet prove Sail retirement or the complete mixed memory history.

Twenty-four new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,842 roots. All
previous roots remain present. The final bounded check passed and left no owned
process running. An explicit vector-index bound avoids the earlier memory-cap
failure. Resource limits stay unchanged. The fixed setup source bridge, other
split arithmetic workers and the full unsigned target remain open. Full
validation remains pending.

### Native chi5 call-ABI obligation

A successful reference control read now identifies the unique native blessed
call. The proof covers all 361 control words. Initialized pointer words recover
the exact supported reference pointer. Pointer alignment excludes low-limb
carry and word overflow for every state lane. Each actual RAM port then has
the original reference cell address. Both native lane halves have the exact
reference thirty-two-bit values.

Twelve new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,854 roots. All
previous roots remain present. The last bounded group passed and left no owned
process running. Sail write execution and the combined native history remain
open. The fixed setup source bridge and the full unsigned target remain open.
Full validation remains pending.

### Native chi5 Sail call-execution obligation

The actual native chi5 history now executes the original complete split call.
The proof projects the complete write list to the original reference writes.
It includes both registers, all lane halves and the Sail frame. Actual reads
recover every input lane. The imported equations prove each output lane.
The proof uses the explicit supported reference ABI, initialized pointer bound,
actual per-port observations and exact history permutation. The full mixed
history must still supply these intermediate facts.

Four new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,858 roots. All previous
roots remain present. Both cache modes passed the last bounded check. It left
no owned process running. The fixed setup source bridge, column-parity and
theta/rho call effects, and the full unsigned integration remain open. Full
validation remains pending.

### Native column-parity controller obligation

The retained parity controller now proves the original control transitions.
It selects the iota round only for iteration zero. It includes the final call
in round twenty-four. The separate slot table retains all six original physical
slots and the native execute-key offset. The leading padding row stays explicit.
The importer compares every selected value with the complete native source.
The kernel proves the emitted row properties and static-table soundness.

Seven new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,865 roots. All previous
roots remain present. The proof reuses the established kernel-checked slot cache.
The last bounded group passed and left no owned process running. Resource caps
stay unchanged. Parity arithmetic and call execution remain open. The fixed
setup source bridge, theta/rho call effect and full unsigned integration remain
open. Full validation remains pending.

### Native parity slot-key and byte-iota obligations

Exact slot-table membership now binds all six original physical lanes. The
proof checks the full control key and rejects the padding row for a live key.
The native byte-iota table now proves both byte bounds and the exact output.
Seven columns reuse the established imported iota data. The counter column has
a different RLE partition. A kernel proof shows that its values agree with the
original arithmetic reference. The proof retains every physical column.

Eight new roots passed focused kernel and axiom checks. They use only the three
allowed axioms. The explicit inventory now contains 12,873 roots. All previous
roots remain present. The final bounded group passed and left no owned process
running. Five-input parity arithmetic, native parity call execution, theta/rho
call execution, the fixed setup source bridge and full unsigned integration
remain open. Full validation remains pending.

### Native five-input parity lookup obligation

The actual five-input XOR table now proves the exact nibble operation. It bounds
all five inputs and the output. It preserves the zero field and native tag 64.
The literal importer checks all 8,388,608 values in the eight physical columns.
It stores shared literal nodes. The output uses sixteen nodes. Kernel proofs
check all 256 output transitions and the actual key-column transitions. They
derive the operation on every row. The proof adds no expected-result premise.

Nineteen new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,892 roots. All
previous roots remain present. The last bounded group passed and left no owned
process running. The packed-checker pilot stays unchanged. Native parity query
binding and call execution, theta/rho call execution, the fixed setup source
bridge and full unsigned integration remain open. Full validation remains
pending.

### Native parity generic-setup and query obligations

The complete parity setup view now retains all four native regions and physical
zero padding. A streaming regression reads the current source file. It compares
all 33,554,432 physical cells. It also checks every retained view's source bytes.
The regression passed. Kernel proofs select the exact region from each native
query discriminator. Both native cache modes now enforce all twenty-two actual
generic queries. The four byte-iota queries prove their exact byte operation.
The sixteen parity queries prove their exact five-input nibble operation.

Twenty new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,912 roots. All
previous roots remain present. The final bounded checks passed and left no owned
process running. The source comparison is a runtime fidelity check. It does not
close the formal JSON source bridge. Native parity lane effects and Sail call
execution, theta/rho call execution, the source bridge and full unsigned
integration remain open. Full validation remains pending.

### Native parity lane-effect obligation

Both native cache modes now prove the complete parity lane result. The proof
uses the actual twenty-two generic queries and all six physical lanes. It
derives each written limb from the queried nibbles. It proves the complete
five-input XOR. The four readonly inputs keep their values. The first lane
uses the four actual byte-iota queries and the three native linear equations.
Its complete write equals its read XOR the selected original round constant.
The native controller selects that constant only on the first column. It
also binds the original control transition and all six physical slots.
`parity_native_reference_schedule` gives the unchanged `Call.result` equality.
The proof adds no result or operand premise.

Fifty-two new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,964 roots. All
12,912 previous roots remain present. Earlier combined reference checks
reached the memory cap. The final proof separates the finite reference
calculation from the native values. The last bounded group passed. It used
633 MiB of physical memory and left no owned process running. Resource caps
stay unchanged. Native parity Sail call execution, theta/rho call execution,
the formal setup source bridge and full unsigned integration remain open.
The packed-checker pilot stays unchanged. Full validation remains pending.

### Native parity Sail call obligation

`parity_call_executes` now proves the original complete parity `Call.Executes`
relation. Both native cache modes pass. The proof binds the actual control and
pointer registers. It checks all twelve lane halves and the full native write
list. The initialized pointer leaves room for every state and scratch slot.
The proof retains initialized read-word bounds, exact event permutation,
actual read observations and `SailHistory`. These premises also bound the old
scratch input. The parity equations do not constrain that old input. The
history proof gives the complete Sail memory frame. It adds no result premise.

Twenty-five new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 12,989 roots. All
12,964 previous roots remain present. The last bounded group passed. It used
627 MiB of physical memory and left no owned process running. Chi5 and parity
now have native call-execution proofs. Theta/rho call execution, the formal
setup source bridge and full unsigned integration remain open. The combined
history must supply the initialized bounds, read observations and event
permutations. The packed-checker pilot stays unchanged. Full frontend checks,
environment audit and baseline refresh, transitive kernel replay and Linux
runtime and warm-cache qualification remain pending.

### Native theta/rho controller and slot obligations

The retained native controller now proves the original control transition and
all five exact column flags. The slot region retains all nine physical
columns. It proves all five state slots and both neighboring parity slots.
Exact slot-key membership rejects the leading padding row. The complete
control key selects the unique original call. The generic controller proof
uses the retained native generic extent. Both region views keep the same
complete source bytes. No production source or reference changed.

Twelve new roots passed focused kernel and axiom checks. They use only the
three allowed axioms. The explicit inventory now contains 13,001 roots. All
12,989 previous roots remain present. The last bounded group passed. It used
649 MiB of physical memory and left no owned process running. Native theta/rho
arithmetic and Sail call execution remain open. The formal setup source bridge
and full unsigned integration remain open. Design items 2 and 3 follow the
machine targets. The packed-checker pilot stays unchanged. Full validation
remains pending.

### Native theta/rho arithmetic lookup obligations

The full unsigned target now has both native theta/rho arithmetic lookup
proofs. `xor_byte_table_sound` proves the complete byte-XOR relation.
`theta_split_table_sound` proves the complete XOR/split relation. The proofs
bound both byte keys and the selected shift. They derive both exact output
fragments. They retain every physical padding field and discriminator.
The native XOR region has 65,536 rows. The native XOR/split region has 524,288
rows. Each region retains all nine physical columns.

Sixteen kernel certificates check every low and high fragment shift.
A general evaluation proof lifts the checked native node transitions to all
rows. The generator supplies finite node correspondences. Kernel proofs check
those correspondences against the imported nodes. The full frontend gate now
checks that the generated correspondence sources are current.

The shared literal importer keeps the exact native region length. It can add
zero encoding slots outside that length. Those slots cannot supply lookup
membership. It checks every original source value after encoding. The two new
regions passed all 5,308,416 source-cell comparisons. Serial proof elaboration
keeps the fragment certificates within the existing resource limits. Earlier
attempts reached the memory cap. The limits stay unchanged.

The final focused group passed 116 source-module checks. It includes the
affected parity consumers and the complete parity source-cell comparison.
All 98 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,099 roots. All 13,001 previous
roots remain present. The last bounded group used 1,773 MiB of physical memory
and left no owned process running. A wider intermediate group stopped safely
after it reached unrelated reference proofs. The final group checks the
affected sources. Generator freshness and Python syntax checks also passed.

Native theta/rho query binding, lane effects and Sail call execution remain
open. The formal setup source bridge and full unsigned integration remain
open. Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend checks, environment audit and baseline refresh,
transitive kernel replay, and Linux runtime and warm-cache qualification
remain pending.

### Native theta/rho fixed-query obligation

The full unsigned target now has all fifty native theta/rho fixed-query
bindings. Both cache modes pass. The eight byte-XOR queries enforce their
complete operation. The forty XOR/split queries enforce both exact shifted
fragments. The two remaining queries select the complete native slot and
control regions. Every query keeps all nine physical fields.

The new composed setup view retains all 4,194,304 physical rows. It selects
each original region at its native offset and retains the trailing zero rows.
All 37,748,736 physical source-cell comparisons passed. The region-selection
proof rejects every wrong discriminator and the physical zero padding.
It adds no operand or expected-result premise. The earlier generic view and
its public proofs remain present.

Both new proof modules passed focused kernel checks. The complete physical
source comparison passed. All 21 new roots passed direct axiom checks. They
use only the three allowed axioms. The explicit inventory now contains 13,120
roots. All 13,099 previous roots remain present. The last bounded proof group
used 724 MiB of physical memory and left no owned process running.

Native theta/rho lane effects and Sail call execution remain open. The formal
setup source bridge and full unsigned integration remain open. Exact lookup,
request and RAM matching stay explicit. Design items 2 and 3 follow the machine
targets. The packed-checker pilot stays unchanged. Full frontend checks,
environment audit and baseline refresh, transitive kernel replay, and Linux
runtime and warm-cache qualification remain pending.

### Native theta/rho byte-input binding obligation

The full unsigned target now has native theta/rho byte-input bindings in both
cache modes. Every state operand has its canonical byte bound. Every fragment
query consumes the same D byte and lane shift as the original native queries.
The D bytes and both fragments have their exact native arithmetic meaning.
Both readonly lanes preserve all four actual memory limbs.

The actual memory-port expressions pack each state read limb from its two
queried bytes. The previous parity lane has the same packing proof. These
equations and native byte bounds give canonical sixteen-bit read values for
all five state lanes and the previous parity lane. The proofs add no input
value or expected-result premise. The next parity lane still needs its
initialization-derived read bounds and its native carry proof.

Both new modules passed focused kernel checks. All 20 new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,140 roots. All 13,120 previous roots remain present. The last
bounded group used 603 MiB of physical memory and left no owned process
running. An explicit small column-index bound removed an earlier elaboration
memory spike. Resource limits stay unchanged.

Native theta/rho rotation, write-lane effects and Sail call execution remain
open. The formal setup source bridge and full unsigned integration remain
open. Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full validation remains pending.

### Native theta/rho next-parity rotation and D-lane obligation

Native constraints now prove the original one-bit next-parity rotation.
The complete D lane equals the previous parity lane XOR that rotation.
`theta_d_native_reference` states this complete native relation. Both cache
modes use the current native equations. The proof uses the four initialized
read limb bounds for the next parity lane. It derives every top bit and carry
from native Boolean assertions and the actual byte-query expressions. No
top-bit value or D result is an input premise.

Both new modules passed focused kernel checks. All 18 new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,158 roots. All 13,140 previous roots remain present. The last
bounded group used 445 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Native theta/rho selected rotations, write-lane effects and Sail call execution
remain open. The formal setup source bridge and full unsigned integration
remain open. The combined history must supply the initialized read bounds.
Design items 2 and 3 follow the machine targets. The packed-checker pilot stays
unchanged. Full validation remains pending.

### Native theta/rho controller, slot and rho-selection obligation

Active native constraints now select the original theta/rho call and all five
exact column flags. Both actual controller queries bind all seven original
physical slots. The slot key retains the complete control word and execute
flag. The native byte shift equals the selected original rho offset modulo
eight. Both cache modes pass. The proof adds no expected-result premise.

The new module and affected consumers passed focused kernel checks. All eight
new roots passed direct axiom checks. They use only the three allowed axioms.
The explicit inventory now contains 13,166 roots. All 13,158 previous roots
remain present. The last bounded group used 601 MiB of physical memory and
left no owned process running. The slot theorem's comment now gives its actual
seven-lane scope. Its public statement stays unchanged.

Native theta/rho write-lane equations, complete lane effects and Sail call
execution remain open. The formal setup source bridge and full unsigned
integration remain open. Design items 2 and 3 follow the machine targets. The
packed-checker pilot stays unchanged. Full validation remains pending.

### Native theta/rho write-equation obligation

Native constraints now prove all twenty actual theta/rho write equations.
Each equation uses all five native flags and the original rho byte placement.
Exact column flags select each written limb's original rho expression. Both
cache modes pass. The proof derives the equations from the imported native
assertions. It adds no write-value or expected-result premise.

The new module passed focused kernel checks. All four new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,170 roots. All 13,166 previous roots remain present. The last
bounded group used 1,368 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Canonical write bounds, complete theta/rho lane effects and Sail call execution
remain open. The formal setup source bridge and full unsigned integration
remain open. Design items 2 and 3 follow the machine targets. The packed-checker
pilot stays unchanged. Full validation remains pending.

### Native theta/rho complete lane-effect obligation

Both native cache modes now prove the complete original theta/rho lane effect.
The actual write limbs have canonical sixteen-bit values. All twenty write
limbs pack the exact original byte rotation. The complete output lane equals
the original state lane XOR the native D lane, followed by the original rho
rotation. The native controller selects the original call and all seven
physical slots. Both parity-input lanes stay unchanged.

`theta_native_reference_schedule` gives the unchanged complete call reference.
The proof keeps the initialized next-parity read bounds explicit. Native
assertions derive all four top bits and carries. Exact native lookup membership
derives every byte XOR and fragment. The proof adds no expected-result premise.

All six new modules passed focused kernel checks. All 26 new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,196 roots. All 13,170 previous roots remain present.
The byte-rotation kernel check used 1,596 MiB of physical memory. The final
native group used 476 MiB. Both checks left no owned process running. The proof
groups the sixty-four rotations into eight declarations. Resource limits stay
unchanged.

Native theta/rho Sail call execution and full unsigned integration remain open.
The combined history must supply the initialized read bounds. The formal setup
source bridge remains open. Design items 2 and 3 follow the machine targets.
The packed-checker pilot stays unchanged. Full frontend validation, environment
audit, baseline refresh, transitive replay and Linux qualification did not run.

### Native theta/rho Sail call obligation

`theta_call_executes` now proves the original complete theta/rho call from the
actual native memory ports. Both cache modes pass. The proof binds the exact
control word, pointer, seven physical slots and fourteen lane halves. It binds
every actual write to the original call write list.

The proof keeps initialized read bounds, exact read observations and the exact
event permutation explicit. Those read bounds supply the next-parity carry
proof. Native constraints bound state writes. Readonly parity refreshes retain
their initialized values. No result value or lane-effect premise is an input.
Production circuits and Rust stay unchanged.

All eleven new modules passed focused kernel checks. All 27 new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,223 roots. All 13,196 previous roots remain present.
The bounded group used 514 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The combined native split-call chain and full unsigned integration remain open.
The formal setup source bridge remains open. Design items 2 and 3 follow the
machine targets. The packed-checker pilot stays unchanged. Full frontend
validation, environment audit, baseline refresh, transitive replay and Linux
qualification did not run.

### Native split-pool controller and call-dispatch obligations

`fixed_control_setup_facts` derives the two controller facts from exact
membership in the complete retained native tables. `fixed_memory_history`
uses those facts with native equations and exact logical RAM matching. It
proves address preservation and strict read-before-write order for every
physical split port. No controller-semantic premise is an input.

`native_call_executes` dispatches each actual split row to the original
complete Sail call. It covers parity, theta/rho and chi5 in both cache modes.
It keeps initialized read bounds, exact read observations and the event
permutation explicit. These proofs use `fixedSetup`, the complete retained
tables. The original JSON source-to-table obligation remains separate and open.

All three new modules passed focused kernel checks. All four new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,227 roots. All 13,223 previous roots remain present.
The final bounded group used 473 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned integration must connect these native worker calls to the same
initialized CPU history. It must close the formal setup source bridge. The
complete native 361-call chain must connect to the proved physical schedule.
Design items 2 and 3 follow the machine targets. The packed-checker pilot stays
unchanged. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.

### Native complete split-permutation obligation

`native_permutation_of_initialized_chain` now proves the original Keccak
permutation from all 361 actual native split calls. Both cache modes pass.
The theorem uses the current imported equations and the complete retained
native setup tables. It adds no expected output or physical-step premise.

The proof binds each call index to its actual reference control read. It
derives distinct aligned write destinations and all final touched words.
Every untouched physical word retains its prior value. Exact low and high
word reads identify each complete canonical lane. These facts prove the
original physical micro-step for each native row. The existing complete
schedule theorem then gives the original permutation.

The theorem keeps initialized Sail histories, exact event permutations, read
observations, public arguments and physical snapshots explicit. The unused
padding lane has value zero and needs no initialized memory cell. Full unsigned
integration must derive these histories and snapshots from the combined CPU
and worker memory argument. It must also close the formal JSON source-to-table
bridge. The original full unsigned target stays unchanged.

All eight new modules passed focused kernel checks. All 20 new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,247 roots. All 13,227 previous roots remain present.
The final bounded group used 491 MiB of physical memory and left no owned
process running. Generic list proofs replaced a large finite destination
check. Explicit lane-pair arguments removed an elaboration timeout. Resource
limits stay unchanged.

The combined full unsigned machine proof remains open. Design items 2 and 3
follow the machine targets. The packed-checker pilot stays unchanged. Full
frontend validation, environment audit, baseline refresh, transitive replay
and Linux qualification did not run.

### Native split combined-history write-bound obligation

`native_write_words_bounded` proves canonical raw write-word limbs for all
three split workers in both cache modes. Exact native equations and the
complete retained tables derive the control and state write bounds. Pointer
and readonly refreshes retain their initialized input bounds. No Sail history,
call argument or expected result is an input to this bound proof.

`native_write_rule` places each split row inside an arbitrary combined memory
pool. All actual ports write at the same imported offset two. The common time
induction can therefore supply all row read bounds and obtain each raw write
bound. This closes the split-worker component of the combined history's
write-bound rule. It does not assume the worker result or a separate split RAM
permutation.

Both new modules passed focused kernel checks. All five new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,252 roots. All 13,247 previous roots remain present.
The bounded group used 514 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The complete combined CPU and worker history still needs its clock facts,
path execution and initialization connection. The formal setup source bridge
remains open. Design items 2 and 3 follow the machine targets. The packed-checker
pilot stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned combined-history clock and order obligations

`unrolled_request_times_unique` derives unique clocks for the complete native
caller set. `unrolled_request_clock_bounds` uses the exact combined request
permutation. It bounds every standard and split worker invocation. It also
proves exact live matching and unique live fulfillment clocks. No separate
worker permutation or typed decoder premise is an input.

`unrolledFullMemoryData` retains one architectural RAM pool. It contains all
CPU, standard worker and split worker edges. `unrolled_full_write_clocks`
bounds every produced clock. `unrolled_full_memory_clocks` uses exact combined
RAM matching to bound every read clock. `unrolled_full_memory_facts` derives
address preservation and strict read-before-write order for the complete pool.
The CPU's omitted virtual port has the native zero-clock token. The split
ports use the current derived-borrow equations. Seed clock bounds and fixed
controller provenance remain explicit. These are supporting obligations of
the unchanged full unsigned target.

All three new modules passed focused kernel checks. All six new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,258 roots. All 13,252 previous roots remain present.
The final bounded group used 531 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

The combined history still needs its complete write rules, path execution
and initialization connection. The formal setup source bridge remains open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned combined-history raw write-rule obligation

`unrolled_full_ordinary_source` obtains the exact public instruction for each
non-caller row. `unrolled_full_cpu_write_rule` proves raw write bounds for all
six CPU families inside an arbitrary ambient history. Both caller classes
use the imported zero-destination equations. Ordinary rows use their original
instruction and physical ROM image. The proof does not equate the physical
ROM image with the verifier's native zero seed.

`unrolled_full_memory_write_rules` combines CPU, standard worker and split
worker rules in the same architectural pool. Chronological induction supplies
each row's read bounds. The proof keeps standard round masks and the split
equations under the complete retained tables explicit. Supported public use
must derive the round masks. The formal source bridge must transfer the
accepted split equations to those retained tables. These supporting premises
do not change the full unsigned target.

Both new modules passed focused kernel checks. All three new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,261 roots. All 13,258 previous roots remain present.
The final bounded group used 530 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

The combined history still needs zero-register preservation, path execution
and its initialization connection. The public round-control and formal setup
source obligations remain open. Design items 2 and 3 follow the machine
targets. The packed-checker pilot stays unchanged. Full frontend validation,
environment audit, baseline refresh, transitive replay and Linux qualification
did not run.

### Full unsigned combined-history zero and realization obligations

`port_not_zero` checks all imported split port addresses in both cache modes.
Every port accesses a nonzero register or the separate RAM space. The result
needs no witness bounds. `unrolled_full_memory_zero_rules` proves zero-register
preservation for the complete CPU and worker pool. Caller writes use the
native zero equations. Ordinary writes use the exact public instruction.

`unrolled_full_memory_history` assembles the combined native history proof.
It derives zero seed values from initialized Sail reads and canonical seed
words. It then proves every raw read and write bound, every terminal word
bound, one exact Sail history and each terminal memory observation. No
separate CPU or worker RAM permutation is an input.

This supporting theorem keeps native initialization, public round masks and
split setup interpretation explicit. The target proof must derive them from
its existing public inputs. Physical ROM initialization remains separate from
the native verifier seed. The full unsigned target stays unchanged.

All three new modules passed focused kernel checks. All three new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,264 roots. All 13,261 previous roots remain present.
The final bounded group used 538 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned path execution and initialization integration remain open.
The public round-control and formal setup source obligations remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned combined worker-schedule obligation

`unrolled_full_requests_match` removes zero-clock fulfillments with the
actual native activity and timestamp equations. Exact combined matching then
accounts for every worker row. `unrolled_full_fulfillment_times_unique`
excludes shared invocation clocks across both worker pools.

`unrolled_full_fulfillment_slot` obtains an actual selected CPU caller for
each fulfillment. The invocation clock equals the caller's initial clock plus
one. `unrolled_full_standard_worker_slot` and `unrolled_full_split_worker_slot`
place all physical worker events in that caller's final cycle slot. Both
split cache modes use their current imported offset two. No decoder registry,
worker occurrence plan or separate request permutation is an input.

The new module passed focused kernel checks. All five new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,269 roots. All 13,264 previous roots remain present. The final
bounded group used 536 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Full unsigned path execution and initialization integration remain open.
The public round-control and formal setup source obligations remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned exact instruction-window obligation

`unrolled_full_fulfillment_window` proves an exact instruction-window test.
A fulfillment event lies in a CPU cycle if and only if that CPU row selects
the same full-width request. Aligned state clocks and unique caller times
exclude every other cycle. The standard and split event-window theorems apply
this result to each actual physical port. Both split cache modes pass.

`unrolled_cpu_event_time` derives each CPU event's native access slot.
`unrolled_cpu_event_window` proves that each CPU event lies in exactly its
own instruction window. The proof covers all six CPU families and both
caller forms. These results supply the exact window membership needed to
extract native calls from the combined history. They add no occurrence plan
or per-worker permutation premise.

Both new modules passed focused kernel checks. All five new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,274 roots. All 13,269 previous roots remain present.
The final bounded group used 535 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned path execution and initialization integration remain open.
The public round-control and formal setup source obligations remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned exact event-group obligation

`unrolled_full_instruction_events` partitions the actual combined event list
at each native instruction window. The group contains exactly that row's
CPU events, its matched standard worker events and its matched split worker
events. The theorem gives an equality of lists. It retains native row order
and leaves chronological permutation to the shared history proof.

`unrolled_full_ordinary_events` proves that an ordinary instruction window
contains only its own CPU events. No worker from either pool can enter that
window. These results close exact event grouping for full unsigned path
extraction. They assume no worker occurrence plan or separate RAM argument.

The new module passed focused kernel checks. Both new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,276 roots. All 13,274 previous roots remain present. The final
bounded group used 531 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Full unsigned path execution and initialization integration remain open.
The public round-control and formal setup source obligations remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned caller-history extraction obligation

The two caller event theorems reduce each full native caller window to its
own CPU events and one matched worker. Unique invocation times select the
worker. The native CSR values exclude contributions from the other pool.
This result covers standard and split callers in both split cache modes.

`unrolled_full_caller_zero_ports` uses exact public decoder matching to prove
that both architectural CPU ports address x0. The two caller history theorems
then extract each worker's exact Sail history from the combined history.
They remove only the CPU x0 events. The extracted event list is a permutation
of every actual worker port. The prefix and suffix histories keep the same
caller boundaries. No separate worker RAM permutation or expected effect
is an input.

All three new modules passed focused kernel checks. All five new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,281 roots. All 13,276 previous roots remain present.
The final bounded group used 529 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned path execution still needs native input observations at these
boundaries and public supported-use controls. Initialization integration and
the formal setup source bridge remain open. Design items 2 and 3 follow the
machine targets. The packed-checker pilot stays unchanged. Full frontend
validation, environment audit, baseline refresh, transitive replay and Linux
qualification did not run.

### Full unsigned native split input-observation obligation

`history_unique_address_read` derives a cell's initial read when its address
occurs once in the actual history. Other addresses may repeat. The native
register proofs check that control and pointer registers each occur once in
every split layout. Their initial observations need no lane-address premise.

`native_call_addresses_distinct` uses these actual register reads and the
public call arguments. It derives the original aligned lane layout from the
native controller and pointer equations. The complete native write projection
then supplies distinct addresses for every real port. Both cache modes pass.

`native_call_input_observations` derives every remaining native read from the
same initialized history. `native_call_executes_of_history` proves the original
complete split call. It no longer takes input observations or address
distinctness as premises. Public call arguments, canonical raw read bounds,
initialized cells and exact event matching remain explicit. The complete
retained fixed tables still need the formal JSON source bridge.

All three new modules passed focused kernel checks. All nine new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,290 roots. All 13,281 previous roots remain present.
The final bounded group used 480 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

Full unsigned path execution must connect the extracted caller windows to
these native calls and derive supported public arguments. Initialization
integration and the formal setup source bridge remain open. Design items 2
and 3 follow the machine targets. The packed-checker pilot stays unchanged.
Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.

### Program parameter migration: public query interpretation

The native row factories now bind ROM words to the initial Sail state.
The unrolled factory selects the public decoder columns by CPU family.
The unified factory selects its public decoder columns in both cache modes.
No factory takes a decoded instruction or expected worker result.

Generic query proofs separate decoder, ROM and fixed helper tags. Decoder
queries retain the full payload. An active PC rejects missing-row sentinels.
ROM queries give the public word at a bounded native word index. Fixed helper
queries retain the original captured row.

The public setup masks now prove each decoder payload width from native
metadata. These proofs cover all 14 CPU profiles. The public decoder lookup
lemmas use these widths and reject decoder padding. Their operand equality
is still a proof obligation for the native circuit adapters.

All five new modules passed focused kernel checks. The last group passed
in four seconds. Peak physical memory was 440 MiB. All 26 new roots passed
direct axiom checks with only the three allowed axioms. The inventory has
17,399 roots. It retains all 17,373 prior roots. Each guard cleaned its
owned children.

Native operand transport, ROM constraint transport and the legacy compiler
execution migration remain open. The production OS binary comparison and
verified checker rollout also remain open. Both cache modes remain required.
Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.

### Full unsigned native split caller-retirement obligation

`unrolled_full_split_memory_call` connects each actual split caller window
to the original complete memory-call relation. The combined pool supplies
all raw read bounds. Its prefix history supplies readable cells at the call.
Supported public arguments remain explicit at this extracted boundary.

`unrolled_full_split_caller_source` identifies the public split instruction,
its full PC and its actual worker kind. The proof uses exact decoder lookup
and the complete request CSR. Standard worker CSRs cannot alias a split CSR.
`unrolled_full_split_pc_binding` derives canonical PC limbs, the four-byte
advance and original Sail PC retirement from the imported ADD/SUB equations.

`unrolled_full_split_caller_retirement` combines native memory execution with
that PC retirement. It executes the original complete split call between the
actual caller boundaries, with the native start and final PCs. PC preparation
preserves all supported call arguments and tracked cell reads. No native
effect, input observation or retirement result is a premise.

All four new modules passed focused kernel checks. All four new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,294 roots. All 13,290 previous roots remain present.
The final bounded group used 534 MiB of physical memory and left no owned
process running. Resource limits stay unchanged.

The full path proof must still derive supported public arguments at each
reachable boundary and connect ordinary and standard worker cycles.
Initialization integration and the formal setup source bridge remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned ordinary-history and MUL/DIV execution obligations

`unrolled_full_ordinary_history` extracts the exact native instruction
history from the combined memory pool. It covers all six CPU families.
It supplies raw bounds for each actual CPU read port. The proof uses the
common ordered history and the exact global event permutation.

`unrolled_full_muldiv_execution` connects that history to the original
Sail MUL/DIV instruction. The public registry supplies the source and
decoder query. The native first read port supplies the operand bound.
The result uses the actual native start and final PCs.

Both new modules passed focused kernel checks. Both new roots passed
direct axiom checks. They use only the three allowed axioms. The explicit
inventory now contains 13,296 roots. All 13,294 previous roots remain
present. The final bounded group used 531 MiB of physical memory and
left no owned process running. Resource limits stay unchanged.

The full path proof must still connect the remaining ordinary and standard
worker cycles. It must derive supported public arguments at each reachable
boundary. Initialization integration and the formal setup source bridge
remain open. Design items 2 and 3 follow the machine targets. The packed
checker pilot stays unchanged. Full frontend validation, environment audit,
baseline refresh, transitive replay and Linux qualification did not run.

### Full unsigned subword execution obligation

`unrolled_full_subword_execution` executes all six original Sail subword
load and store forms at their actual shared-history boundaries. The public
registry supplies the source and full decoder query. The native history
supplies each initialized port address. Common read bounds and native
equations supply the effective address, containing word and byte offset.

The proof handles RAM and ROM. The same readonly prefix preserves public
ROM bytes. Those bytes give each ROM lookup its original Sail meaning.
The physical image stays separate from the verifier's raw boot seed.

The new module passed its focused kernel check. The new root passed its
direct axiom check. It uses only the three allowed axioms. The explicit
inventory now contains 13,297 roots. All 13,296 previous roots remain
present. The bounded group used 554 MiB of physical memory and left no
owned process running. Resource limits stay unchanged.

Full unsigned composition, supported-use derivation, initialization
integration and the formal setup source bridge remain open. Design items
2 and 3 follow the machine targets. The packed-checker pilot stays unchanged.
Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.

### Full unsigned stream-position obligation

`unrolled_full_cycle_count` derives each cycle's exact stream increment from
native clocks and state matching. `unrolled_full_initial_count` proves the
initial count is zero. `unrolled_full_terminal_count` proves the final count
includes each external read once. These results cover all six CPU families.

`unrolled_full_caller_read_disabled` proves that standard and split callers
consume no stream word. It uses exact public lookup and the imported packed
selector equations. It does not require a separate caller decoder registry.

The new module and all four roots passed focused kernel and direct axiom
checks. They use only the three allowed axioms. The explicit inventory now
contains 13,301 roots. All 13,297 previous roots remain present. The bounded
group used 540 MiB of physical memory and left no owned process running.
Resource limits stay unchanged.

Full unsigned composition, supported-use derivation, initialization
integration and the formal setup source bridge remain open. Design items
2 and 3 follow the machine targets. The packed-checker pilot stays unchanged.
Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.

### Full unsigned six-family ordinary-cycle obligation

`unrolled_full_ordinary_cycle` now executes every ordinary full native row
at its actual shared-history cuts. It covers arithmetic, modular operations,
external input, word memory, subword memory, shifts, bitwise operations,
control flow and multiply/divide. Each case uses its original Sail clause.
The result includes the exact stream increment and native PC endpoints.

`unrolled_full_ordinary_context` retains the filtered cycle history and its
canonical native order. `unrolled_full_pc_bounds` derives both PC endpoint
bounds from public queries, native state matching and verifier closure.
The subword shared-history lemma supports the complete cycle dispatch.
All previous public theorem statements stay unchanged.

The cycle proof derives raw x0 reads from the same Sail history and common
word bounds. It has no separate zero-value premise. Public configuration,
physical image, readonly ROM history and exact native matching stay explicit.

All changed modules and four new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,305 roots. All 13,301 previous roots remain present. The
bounded group used 547 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Standard-worker call integration, full path composition, supported-use
derivation, initialization integration and the formal setup source bridge
remain open. Design items 2 and 3 follow the machine targets. The packed
checker pilot stays unchanged. Full frontend validation, environment audit,
baseline refresh, transitive replay and Linux qualification did not run.

### Full unsigned standard-worker caller-cycle obligation

`unrolled_full_standard_caller_cycle` connects bigint and extended-round
workers to their actual caller cuts in the shared history. Each cycle
executes the original complete memory-call relation and Sail PC retirement.
The public source remains valid at the call. Native start and final PCs
match the same public instruction.

`unrolled_full_standard_addresses_distinct` derives port separation from
the complete initialized pool and exact matching. The observation theorem
then derives every input read. The worker-call theorem proves both native
call relations. The source and PC theorems connect full public lookup to
the actual matched worker. No call result, per-port observation or address
separation is a premise.

Commands, round controllers and worker RAM domains stay explicit. The
supported-use proof must derive them at reachable boundaries. The common
initialized boundary, raw bounds and exact matching also stay explicit.

All five new modules and six roots passed focused kernel and direct axiom
checks. They use only the three allowed axioms. The explicit inventory now
contains 13,311 roots. All 13,305 previous roots remain present. The bounded
group used 535 MiB of physical memory and left no owned process running.
Resource limits stay unchanged.

Full path composition, supported-use derivation, native ROM interpretation,
initialization integration and the formal setup source bridge remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned split-cycle and event-boundary obligations

`unrolled_full_split_caller_cycle` connects each split worker to its full
actual caller window. It retains the public source at that cut, the complete
native memory-call relation and original Sail retirement. Supported control
and pointer arguments remain explicit at the extracted boundary. Both cache
modes retain all actual native ports.

`unrolled_full_event_interval` places every CPU and worker event between
the native initial and terminal clocks. The complete combined request
permutation supplies each worker's slot. No separate worker schedule is
assumed. These results close the local split-cycle and event-boundary
obligations for full path composition.

Both modules and roots passed focused kernel and direct axiom checks. They
use only the three allowed axioms. The explicit inventory now contains
13,313 roots. All 13,311 previous roots remain present. The bounded group
used 537 MiB of physical memory and left no owned process running. Resource
limits stay unchanged.

Full path composition, supported-use derivation, native ROM interpretation,
initialization integration and the formal setup source bridge remain open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned physical-history path-composition obligation

`unrolled_full_cycle_transition` joins all six ordinary CPU families,
standard workers and split workers in one stream-indexed reference step.
It derives each native instruction and complete call result. The first
step starts from the original public Sail state. Later steps use the same
actual history cuts and native PCs.

`unrolled_full_physical_execution` composes the complete native state path.
It proves the combined full reference relation, terminal PC, tracked terminal
reads and exact total stream consumption. It uses the same initialized
physical history and exact combined matching throughout. It assumes no
instruction or worker execution result.

This theorem closes physical-history path composition. It is not yet a
proof of `UnrolledFullUnsigned`. The following named obligations remain:

1. Derive standard commands, round controllers and worker RAM domains from
   public supported use. Derive split arguments at each reachable caller cut.
2. Interpret native zero ROM tokens in the complete combined pool.
3. Connect the actual initialization boundary to that interpreted execution.
4. Prove the JSON source-to-fixed-setup bridge stated in `FixedSetup`.

Both new modules and roots passed focused kernel and direct axiom checks.
They use only the three allowed axioms. The explicit inventory now contains
13,315 roots. All 13,313 previous roots remain present. The bounded group
used 535 MiB of physical memory and left no owned process running. Resource
limits stay unchanged.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned combined-pool ROM-interpretation obligation

`unrolled_full_rom_acceptance` now preserves full native acceptance under
public ROM interpretation. The proof covers all six CPU families and the
combined standard and split worker pools. CPU transfer projection uses
canonical addresses from that same native pool. It handles selected callers
through their two architectural x0 ports.

The complete transfer projection preserves exact state, request and RAM
permutations. `unrolled_full_rom_lookup` preserves every full-width public
decoder query. `unrolled_full_rom_unchanged` proves that each interpreted ROM
transfer refreshes its original public word. No alternate worker permutation
or execution result is a premise.

Worker RAM-domain contracts remain explicit. They keep standard and split
transfers fixed. Supported use must still derive those contracts together
with commands, round controls and split arguments at reachable caller cuts.
The native boot seed remains separate from the physical public byte image.

The new module and five roots passed focused kernel and direct axiom checks.
They use only the three allowed axioms. The explicit inventory now contains
13,320 roots. All 13,315 previous roots remain present. The bounded group
used 534 MiB of physical memory and left no owned process running. Resource
limits stay unchanged.

Public supported-use derivation, initialization-to-execution integration
and the formal setup source bridge remain open. Design items 2 and 3 follow
the machine targets. The packed-checker pilot stays unchanged. Full frontend
validation, environment audit, baseline refresh, transitive replay and Linux
qualification did not run.

### Full unsigned zero-boot execution-adapter obligation

`unrolled_full_boot_execution` now starts from the native zero boot image.
It constructs the physical initialized history through public ROM
interpretation. It derives common raw bounds, every cycle's execution,
terminal observations and exact stream consumption. The existing standalone
initialization-to-boot adapter supplies this theorem's boot interface.
The result returns the unchanged native terminal tokens through `ROMView`.

Round masks follow from the explicit round controller contract and native
packing equations. Exact lookup, request and RAM matching stay explicit.
No instruction, call result or completed reference trace is a premise.

The new module and root passed focused kernel and direct axiom checks.
It uses only the three allowed axioms. The explicit inventory now contains
13,321 roots. All 13,320 previous roots remain present. The bounded group
used 547 MiB of physical memory and left no owned process running. Resource
limits stay unchanged.

Two full-target obligations remain. Public supported use must supply
commands, round controls, worker RAM domains and split arguments at actual
caller cuts. The formal JSON source-to-fixed-setup bridge must supply the
canonical setup interpretation. The full target statement stays unchanged.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned accepted-prefix obligation

`unrolled_full_prefix_accepted` constructs an accepted native prefix before
any actual positive-clock CPU boundary. It retains the same standard and
split setup data and both cache modes. The exact native memory split gives
the prefix its terminal frontier and preserves the full suffix facts.

The three prefix functions select actual CPU and worker rows. The transfer
theorem proves that they select exactly the writes before one common cut.
The request theorem restricts the complete combined ledger to that cut.
State matching restricts to the actual next CPU state. No independent prefix
match, command, round mask, supported argument or reference result is used.

All three new modules and six roots passed focused kernel and direct axiom
checks. They use only the three allowed axioms. The explicit inventory now
contains 13,327 roots. All 13,321 previous roots remain present. The bounded
group used 539 MiB of physical memory and left no owned process running.
Resource limits stay unchanged.

This closes native prefix construction for supported-use induction. Public
supported use must still supply the worker input contracts. The formal setup
source bridge also remains open. Design items 2 and 3 follow the machine
targets. The packed-checker pilot stays unchanged. Full frontend validation,
environment audit, baseline refresh, transitive replay and Linux qualification
did not run.

### Full unsigned prefix-frontier input obligations

`unrolled_full_prefix_worker_read` proves that a nonzero worker read in
the caller's final native slot comes from the exact prefix frontier. CPU
writes earlier in that cycle touch x0. Standard and split workers occupy
aligned final slots. Exact suffix matching excludes an intervening write.
No input value, valid command or reference result is assumed.

`unrolled_full_prefix_boot` preserves the public boot interface at the actual
prefix endpoint. Full public queries bound that endpoint's PC. Native clock
equations bound its timestamp. The accepted prefix closes the same typed
verifier boundary.

`unrolled_full_boot_execution_and_bounds` retains canonical terminal-word
bounds beside complete boot execution. These bounds let supported-use
induction recover worker registers from native frontier tokens. The existing
boot-execution theorem keeps its original public statement.

All changed modules and three new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,330 roots. All 13,327 previous roots remain present. The
bounded group used 563 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Public supported-use induction and the formal setup source bridge remain
open. Design items 2 and 3 follow the machine targets. The packed-checker
pilot stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned reachable-input conversion obligations

`unrolled_full_supported_standard_inputs` converts reachable public full
reference arguments into native standard-worker commands, round controls
and RAM domains. The proof uses bounded actual frontier observations. It
reuses one extracted native ABI argument proof. The existing unified stream
reference theorem keeps its original public statement.

`unrolled_full_supported_split_inputs` obtains the blessed split index and
register arguments from public full-reference reachability. The native
split RAM-domain theorem then locates every actual port. It uses only the
pointer-word bound and two register observations. Native lane-value bounds
and an expected operation result are not premises. Both cache modes and
all three split layouts use their complete port enumeration.

All changed modules and four new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,334 roots. All 13,330 previous roots remain present. The
bounded group used 541 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The full native-prefix induction must connect these converters to the
proved boot execution and frontier facts. The formal setup source bridge
also remains open. Design items 2 and 3 follow the machine targets. The
packed-checker pilot stays unchanged. Full frontend validation, environment
audit, baseline refresh, transitive replay and Linux qualification did not run.

### Full unsigned reusable split-input obligation

`nativeCallArguments` retains only a derived blessed input control, a bounded
pointer word and its public RAM/alignment conditions. It stores no output,
memory effect or execution result. Actual reachable reference observations
prove these facts for the native tokens. The same tokens recover the public
arguments at any actual history cut that observes them.

`unrolled_full_supported_split_native_inputs` derives those reusable facts
and every native port domain from public full-reference reachability. This
removes the reference-state identity from the inputs needed by prefix
induction. Both cache modes retain their actual register ports.

All changed modules and four new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,338 roots. All 13,334 previous roots remain present. The
bounded group used 531 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Full native-prefix induction and the formal setup source bridge remain
open. Design items 2 and 3 follow the machine targets. The packed-checker
pilot stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned native-input execution-interface obligation

`unrolled_full_split_arguments_at_cut` recovers public split arguments from
derived native input tokens at the exact caller cut. Exact combined matching
and initialized history supply its register observations. No lane value or
per-cut argument is assumed by the execution interface.

`unrolled_full_boot_execution_of_native_inputs` now executes the complete
boot trace from reusable standard and split input facts. It proves the full
reference relation and canonical terminal bounds. The native input facts
contain commands, controls, pointers and RAM locations. They contain no
worker output, instruction result or reference trace.

The selected-caller composition interfaces apply these facts at actual
selected callers. All three earlier public composition/execution statements
stay unchanged. Their existing interfaces now use the same kernel-checked
proofs through wrappers. The full machine target also stays unchanged.

All changed modules and five new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,343 roots. All 13,338 previous roots remain present. The
bounded group used 533 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

Full native-prefix induction must still derive all reusable input facts
from public supported use. The formal setup source bridge also remains open.
Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.

### Full unsigned supported-use induction obligation

`unrolled_full_supported_native_inputs` now derives every standard and split
worker input contract from public full-reference supported use. The proof
uses strong induction on the actual caller clock. Each earlier accepted
prefix executes from the original boot state. Its actual terminal frontier
supplies the current worker's bounded register reads.

Native request clocks prove that each earlier worker belongs to a smaller
caller clock. Exact prefix and suffix matching identify every current read
token. Public reachable arguments then give commands, round controls, split
input facts and all worker RAM domains. No native input contract, operation
result or completed reference trace is a premise of this induction.

`unrolled_full_supported_execution` composes those inputs with complete native
boot execution. `unrolled_full_soundness_of_setup_interpretation` connects the
original target and actual standalone initialization interface to that proof.
The wrapper exposes one open importer obligation: parsed fixed JSON must
imply the canonical setup interpretation. The target statement stays unchanged.

All changed modules and five new roots passed focused kernel and direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,348 roots. All 13,343 previous roots remain present. The
bounded group used 554 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The formal setup source bridge remains open. Complete that bridge before
claiming the full target. Design items 2 and 3 follow the machine targets.
The packed-checker pilot stays unchanged. Full frontend validation,
environment audit, baseline refresh, transitive replay and Linux qualification
did not run.


### Full unsigned setup transport obligation

`equations_of_setup_refinement` now transports every native split equation
to a refined fixed table. It preserves every assertion and timestamp query.
The proof covers the three workers in both cache modes.
`control_of_fixed_setup_refinement` derives the native controller facts.

`unrolled_full_soundness_of_source_rows` connects this transport to the
original full target and its initialization adapter. It requires three
`FixedSetupRows` certificates. They cover parity, theta/rho and chi5. Each
certificate must map every parsed physical row, including padding, into the
complete fixed table. All three certificates remain open. No target or
existing premise changed.

The changed modules and six new roots passed focused kernel and direct axiom
checks. They use only the three allowed axioms. The explicit inventory now
contains 13,354 roots. All 13,348 previous roots remain present. The bounded
group used 554 MiB of physical memory and left no owned process running.
Resource limits stay unchanged.

A total JSON decoder prototype stays in the evidence directory. Its small
kernel tests and all 18 retained setup-directory JSON differential checks
passed. Direct kernel source evaluation exceeded the memory cap. The guard
stopped each probe and left no worker running. The prototype is not adopted.
The source certificates still need a compact kernel representation.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.


### Full unsigned source-decoder transparency obligation

`Setup.parse` now uses `Import.SetupJson`. All decoder recursion is total.
`run_append` proves exact source-block composition. `parse_of_run` connects
checked block execution and a checked final state to the decoded JSON.
The kernel can keep earlier array data abstract during a later block check.

Focused checks passed for 101 modules. They include the changed importer,
source-interpretation proofs and complete theta/rho physical-table comparison.
All 18 retained setup-directory JSON files match the earlier parser. Every
decoded artifact field also matches. The edge controls cover numbers, Unicode,
duplicate keys, delimiters and malformed input. All seven named kernel
controls pass. Static setup checks also pass for 16 setup artifacts, 731
native source hashes, 15 production circuits and one derived fixture.

All 18 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,372 roots. All 13,354 previous
roots remain present. The bounded focused group used 769 MiB of physical
memory and left no owned process running. Resource limits stay unchanged.

The decoder keeps the existing 64-bit number bound as an explicit integer.
The retained source bytes, imported values and target statements stay
unchanged. The three `FixedSetupRows` certificates remain open. A separate
block-certificate generator stays in the evidence directory until its kernel
checks pass. No full-source certificate is claimed by the decoder change.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.


### Full unsigned parsed-field transport obligation

`SetupFields` proves that a successful setup parse preserves the complete
column field and the physical domain length. The proof retains the artifact
validation premise. `fixed_setup_rows_of_decoded_columns` connects these
fields to the original `FixedSetupRows` predicate. It includes physical padding.
It does not require a second evaluation of unrelated circuit fields.

The new module passed focused kernel checks. All five new roots passed direct
axiom checks. They use only the three allowed axioms. The explicit inventory
now contains 13,377 roots. All 13,372 previous roots remain present. The bounded
focused group used 399 MiB of physical memory and left no owned process
running. Resource limits stay unchanged.

The separate source-block experiment proved complete theta/rho JSON parsing.
It covered 909,925 bytes in 238 seconds and used 1,308 MiB of physical memory.
It used a character block representation of the same source bytes. This
experiment remains outside the branch. It does not close the three source
table certificates. Those certificates remain open. The parity source has
107,052 RLE block entries but only 283 distinct blocks. The chi5 source has
63,011 entries but only 539 distinct blocks. Reuse these blocks to reduce
certificate cost.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.


### Full unsigned source-array composition obligation

The source composition rules now reuse a checked block at every occurrence.
`eager_array_family` preserves its exact byte order. The column-object rule
preserves the native object format. The decoder rules preserve every block
and its order. `parse_of_eager` gives the exact JSON parse result.

Focused checks passed for all three new modules. All 11 kernel controls pass.
They cover affine, dense and periodic blocks, negative stride, repeated array
entries and column objects. They reject a changed value and a missing comma.
All 23 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,400 roots. All 13,377 previous
roots remain present. The bounded group used 293 MiB of physical memory and
left no owned process running. Resource limits stay unchanged.

The production sources and captures have not changed. The three source-table
certificates remain open. Generate their shared block libraries next. Design
items 2 and 3 follow the machine targets. The packed-checker pilot stays
unchanged. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.


### Full unsigned number-token source obligation

`check_number_token` checks each distinct number spelling. Its soundness
theorem proves the exact value in every array and object context. The check
requires full token consumption and exact JSON number equality. Array and
object composition now use these facts. The shared block generator can reuse
number certificates inside different RLE objects.

Focused checks passed for the importer, source composition rules and their
users. All 18 retained setup-directory JSON differential checks still pass.
All ten new kernel controls pass. They cover signed numbers, exponents,
repeated values and duplicate-key order. They reject incomplete tokens,
trailing characters, wrong values and leading zeros.

All 29 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,429 roots. All 13,400 previous
roots remain present. The bounded focused groups used at most 713 MiB of
physical memory. They left no owned process running. Resource limits stay
unchanged.

The separate parity library experiment also passed. It proves source and
decoder facts for all 283 distinct blocks. These blocks occur 107,052 times.
The experiment used 294 seconds and 1,819 MiB of physical memory. It remains
outside the branch. Number-token reuse now supplies a smaller composition
method for the larger source libraries. The three production source-table
certificates remain open. No target or existing premise changed.

Design items 2 and 3 follow the machine targets. The packed-checker pilot
stays unchanged. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.


### Full unsigned shared source composition obligation

The string checker now has a kernel soundness theorem. One check supplies
both a JSON value and an object key. Shared source nodes compose numbers,
strings, booleans, null values, arrays and objects. Their proofs preserve
source order and the exact JSON result. The source generator can reuse these
proofs for each distinct node.

The string checker rejects characters that require JSON escapes. A runtime
scan found no such characters in the three retained split sources. The source
rules add no restriction to the target statements or to the setup parser.

Focused checks passed for the importer and source rules. The 18 retained
setup-directory JSON differential checks still pass. All 14 new kernel
controls pass. They cover empty strings, spaces, Unicode, keys, both Boolean
values, null values and mixed nodes. They reject quotes, backslashes and
control characters in the unescaped representation.

All 39 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now contains 13,468 roots. All 13,429 previous
roots remain present. The bounded focused groups used at most 749 MiB of
physical memory. They left no owned process running. Resource limits stay
unchanged.

The three production source-table certificates remain open. Generate their
shared source nodes and prove physical row matching next. Design items 2 and
3 follow the machine targets. The packed-checker pilot stays unchanged. Full
frontend validation, environment audit, baseline refresh, transitive replay
and Linux qualification did not run.


### Full unsigned captured-source parsing obligation

The shared table interpreter now proves source parsing for parity, theta/rho
and chi5. Its soundness theorem covers every table and depth. The theorem
uses the proved string and number checks. The object adapter supplies complete
source consumption. Equality proofs retain every byte and JSON value when
array and object children share their evaluation.

The generator retains all keys, values and field order from each source. Its
freshness check passes for all six generated modules. Exact byte comparisons
pass for all 11,980,612 retained source bytes. These comparisons are importer
checks. The kernel proves parsing for each represented source. Runtime code
does not supply a theorem proof. The full validation driver now requires both
generation freshness and exact byte identity.

The focused source group passed 21 checks. It includes all three data imports,
all three parser certificates, the interpreter, the proof generator and its
controls. Eleven new kernel controls pass. They cover field order, array
contents, negative numbers, Unicode, lookup branches, default entries, bounded
cycles and the zero-depth result. They reject an incorrect numeric value.

All 63 new roots passed direct axiom checks. They use only the three allowed
axioms. The explicit inventory now has 13,531 roots. It retains all 13,468
previous roots. The final combined group used 168 seconds and 879 MiB of
physical memory. The separate theta data import used at most 1,701 MiB.
All guards left no owned process running. Resource limits stay unchanged.

The three `FixedSetupRows` certificates remain open. The next step must decode
the retained columns and match every physical row to the original canonical
tables. Padding stays in the physical domain. No target statement or existing
premise changed. The packed-checker pilot stays unchanged.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned RLE decoding obligation

The generic RLE decoding obligation is closed. The proof covers arbitrary
affine blocks, dense arrays and periodic blocks with signed strides. Column
and array decoding retain each entry in its original position. The exact
column JSON now supplies the decoder premise of `FixedSetupRows`. The
adapter retains the complete physical-row membership premise.

The focused source group passed 24 checks. Eleven new kernel controls pass.
They cover mixed block order, the physical end, repeated and empty columns,
and zero repetitions. They reject negative natural values, fractional
strides and missing block fields. Zero repetitions stay in the decoded data;
the existing artifact validator still rejects an empty block.

All 21 new roots and five retained controls passed direct axiom checks. They
use only the three allowed axioms. The explicit inventory now has 13,552
roots. It retains all 13,531 previous roots. The bounded checks used at most
454 MiB of physical memory. They left no owned process running.

Bind the decoder rules to the three captured column arrays next. Then prove
physical row membership in each canonical table, including padding. The
three `FixedSetupRows` certificates remain open. No target statement or
existing premise changed. The packed-checker pilot stays unchanged.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned captured column binding obligation

The three captured column bindings are proved. The kernel checks 283 distinct
parity blocks, 2,100 theta/rho blocks and 539 chi5 blocks. Each certificate
returns the exact retained column array and trace length. It preserves all
8, 9 and 11 columns. Large payload arrays use a shared scalar dictionary and
a general array equality proof. The proof preserves all entries and their
order. Header proofs use that array fact without unfolding the large payload.

Source data and RLE metadata now use separate modules. Declaration checks run
synchronously. The resource limits stay unchanged. Earlier combined imports
and direct checks of a 1,024-value payload exceeded the memory cap. The final
representation and proof rules passed. The theta group used 157 seconds and
1,954 MiB of physical memory. The final combined group passed 28 checks in
71 seconds and used 880 MiB. No guard left an owned process running.

Generation freshness passes for all nine generated modules. Exact byte
comparisons pass for all three original artifacts. The kernel rejects a
changed retained block binding with unchanged source bytes. Three dictionary
controls also pass. One control covers a 1,024-entry array through the general
rule. All 495 new roots pass direct axiom checks. They use only the three
allowed axioms. The inventory now has 14,047 roots. It retains all 13,552
previous roots.

Review now names the remaining predicates: `SplitParityPhysicalRows`,
`SplitThetaPhysicalRows` and `SplitChiPhysicalRows`. Each requires every
physical row to belong to the original canonical table. Padding stays in the
domain. The conditional source adapters passed kernel checks. The original
target setup-source references stay unchanged. Bind the equal byte
representation at that interface when the row certificates are complete.
The three `FixedSetupRows` certificates remain open. The packed-checker pilot
stays unchanged. Design items 2 and 3 still follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned chi5 query transport obligation

The earlier full physical chi5 containment helper is too strong. The canonical
table has 1,048,697 real rows with tags 65 and 66. The physical capture also
has zero padding. The kernel proves that the canonical table excludes the
all-zero row. Keep the old conditional helper for compatibility. Use guarded
source membership for the actual query tags to close the original target.

Guarded transport now passes kernel checks. It preserves every constraint,
assertion and timestamp lookup in both cache modes. The adapter returns the
original `UnrolledFullUnsigned` proposition. The target, canonical table and
original setup premises stay unchanged. This is a proof interface correction.
It does not establish a native circuit defect.

The focused group passed six module checks. Nine new roots passed direct
axiom checks. They use only the three allowed axioms. The inventory now has
14,056 roots. It retains all 14,047 previous roots. The three source-row
membership certificates remain open. Chi5 now uses its actual query tags.
Design items 2 and 3 still follow the machine targets. The packed-checker
pilot stays unchanged.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned chi5 padding exclusion obligation

The kernel now proves that native query tags exclude every chi5 padding
index. The proof uses the exact decoded source tag column. Its adapter
requires canonical membership only for the 1,048,697 real source rows.
The original parsed-source premise supplies the remaining fields. The proof
adds no validation or padding assumption. Real-row membership stays open.

The focused module and its three new roots pass. They use only the three
allowed axioms. The inventory now has 14,059 roots. It retains all 14,056
previous roots. The bounded module check used 411 MiB of physical memory.
No guard left an owned process running. The packed-checker pilot stays
unchanged. Design items 2 and 3 still follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned physical padding obligations

The padding cases are closed. Parsing already proves each column's complete
physical coverage. Exact terminal-block certificates locate its zero tail.
The kernel checks all 28 captured columns. The proof does not expand their
large prefixes. Parity and theta/rho padding rows belong to the original
canonical tables. Native query tags exclude chi5 padding.

The three source adapters now require only the named real-row predicates:
`SplitParityRealRows`, `SplitThetaRealRows` and `SplitChiRealRows`. These
predicates retain parsing, column shape and complete row values. They are
open proof obligations. They are not new assumptions of the machine target.
Bind the equal byte representation at the original source interface when
the row certificates are complete. The full unsigned target remains open.

The shared index decoder preserves the captured values. Its ordinary wrapper
keeps conversion at the named encoding. The terminal-index certificate uses
a short binary arithmetic proof. Earlier drafts hit time or depth limits.
Two owned guards stopped early. Shorter diagnostic guards also timed out.
All guards cleaned their owned children. The guard limits did not increase.

Every affected source representation and parser certificate passed a focused
rebuild. The final padding group passed eight module checks in 26 seconds.
It used 836 MiB of physical memory. Generation freshness and exact byte
identity pass for all three sources. The existing changed-block control
passes. The new controls accept valid padding. They reject a nonzero tail
and an insufficient padding extent. The Python scripts pass syntax checks.
The frontend now requires these controls. The full frontend did not run.

All 122 new roots pass direct axiom checks. They use only the three allowed
axioms. The inventory now has 14,181 roots. It retains all 14,059 previous
roots. The packed-checker pilot stays unchanged. Design items 2 and 3 still
follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned chi5 source input and tag obligations

The five chi5 source input columns now match the original canonical columns.
The proof covers all 1,048,576 arithmetic rows. It uses the retained periodic
and constant blocks. The largest selected input prefix has 256 blocks.
Generic prefix and block-selection rules avoid expansion of the row domain.
The complete retained tag column also equals the original canonical column.

The focused group passed three module checks in six seconds. It used 658 MiB
of physical memory. Eight new roots passed direct axiom checks. They use only
the three allowed axioms. The inventory now has 14,189 roots. It retains all
14,181 previous roots. The source artifacts did not change. The previous
source generation and byte-identity checks still apply.

Chi5 still needs five output column correspondences and its controller rows.
The parity and theta/rho real-row predicates also remain open. Bind the equal
byte representation at the original source interface when these proofs are
complete. The packed-checker pilot stays unchanged. Design items 2 and 3
still follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned chi5 controller source obligation

The chi5 controller source case is closed. Every one of its 121 rows has
canonical lookup membership. The proof preserves all 11 fields. It keeps
the parse, column shape and complete row-value premises explicit. The new
membership theorem uses the retained source representation. Its connection
to the original setup-source interface remains open.

The source index decoder now proves exact suffix extraction. The kernel
checks a bounded suffix for each of the 11 columns. A constructor equation
supplies each index projection. This avoids evaluation of the full index
list. Successful source parsing supplies the complete column coverage.
The kernel then checks all 1,331 controller field equalities. The existing
native controller theorem connects these fields to the original generic table.

The focused group passed seven module checks in 19 seconds. It used 2,313 MiB
of physical memory under the 2,560 MiB cap. Direct native-column comparison
reduced a prior peak of 2,520 MiB. The guard cleaned every owned child. The
padding controls still accept the valid case. They reject both invalid cases.
No source artifact or native table changed. All 41 new roots passed direct
axiom checks. They use only the three allowed axioms. The inventory now has
14,230 roots. It retains all 14,189 previous roots.

Chi5 now needs its five arithmetic output correspondences. The parity and
theta/rho real-row predicates also remain open. Bind the original source
interface when the row certificates are complete. The packed-checker pilot
stays unchanged. Design items 2 and 3 still follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned chi5 outer output obligations

Chi5 source output fields three and four now match the original canonical
columns. The proof covers all 1,048,576 arithmetic rows. It checks each stored
RLE template. Analytic periodic and constant-block rules then supply every
row value. The existing canonical chi theorem connects these values to the
original generic table.

A combined template check exceeded the physical memory cap. The final proof
checks its bounded templates separately. It derives block lengths from their
proved shapes. No limit increased. The final focused group passed three
module checks in 29 seconds. It used 935 MiB of physical memory. Every guard
cleaned its owned children. Four new roots pass direct axiom checks. They use
only the three allowed axioms. The inventory now has 14,234 roots. It retains
all 14,230 previous roots.

Chi5 has three arithmetic output correspondences left. Its five input fields,
tag column, other two output fields and controller rows have kernel proofs.
The parity and theta/rho real-row predicates also remain open. Bind the
original source interface when the row certificates are complete. The packed
checker pilot stays unchanged. Design items 2 and 3 still follow the targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned chi5 middle output obligation

Chi5 source output field two now matches its original canonical column.
The proof covers all 1,048,576 arithmetic rows. A general chunk rule proves
that each stored value covers 256 physical rows. The kernel checks the
40 source templates. It then checks all 4,096 distinct chunk positions.
The rule supports both positive and negative periodic strides.

An array-function representation exceeded the physical memory cap. The
final proof constructs the same arrays with repeated lists. The focused
check passed in nine seconds. It used 553 MiB of physical memory. No limit
increased. The guard cleaned all owned children. No source artifact, native
table or packed-checker pilot changed. Six new roots passed direct axiom
checks. They use only the three allowed axioms. The inventory now has
14,240 roots. It retains all 14,234 previous roots.

Two chi5 arithmetic output correspondences remain. The parity and theta/rho
real-row predicates also remain open. The original source interface still
needs its binding. Design items 2 and 3 follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned chi5 low output obligation

Chi5 source output field zero now matches its original canonical column.
The proof covers all 1,048,576 arithmetic rows. Exact scalar certificates
prove both remaining source index grammars. The first grammar has 54,535
stored block indices. The second has 6,969. Every digit, repeat count and
scalar product enters an ordinary kernel proof. Binary power certificates
avoid a change to the exponentiation limit.

A general cycle theorem supplies every row from short block checks. It
preserves the source prefix and the final partial cycle. It does not read
the later controller or padding rows. The focused low-output group passed
in ten seconds. It used 1,047 MiB of physical memory. The guard cleaned all
owned children. All 23 new roots passed direct axiom checks. They use only
the three allowed axioms. The inventory now has 14,263 roots. It retains
all 14,240 previous roots. No native source artifact or table changed.
The packed checker pilot stays unchanged.

One chi5 arithmetic output correspondence remains. The parity and theta/rho
real-row predicates also remain open. The original source interface still
needs its binding. Design items 2 and 3 follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned chi5 source-row obligation

The complete chi5 real-row obligation is closed. All 1,048,576 arithmetic
rows match the original canonical table in all 11 fields. All 121 controller
rows also have canonical membership. The final arithmetic output uses
16-row chunks. Its 53 templates and its short repeated cycles have kernel
proofs. The general chunk rule now supports any positive scale. The earlier
256-row rule and its public statements stay intact.

The final output check passed in ten seconds. It used 1,082 MiB of physical
memory. The combined membership module passed in four seconds. It used
412 MiB. Each guard cleaned all owned children. The closed real-row theorem
now supplies guarded source membership. The native tags still exclude the
physical zero padding. No parse, row-value or lookup premise changed. No
native source artifact, table or packed-checker pilot changed. All 12 new
roots passed direct axiom checks. They use only the three allowed axioms.
The inventory now has 14,275 roots. It retains all 14,263 previous roots.

Parity and theta/rho real-row membership remain open. The original source
strings still need their byte-equal bindings. FullUnsigned is not yet proved.
Design items 2 and 3 follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned theta/rho control and slot obligations

The theta/rho controller and slot source cases are closed. All 242 rows
match their original physical reference rows in all nine fields. Exact
suffix certificates bind the parsed source columns. Successful source
parsing supplies their complete physical coverage. The row theorem then
supplies canonical membership with the original parse and row-value premises.

The focused group passed in twenty seconds. It used 2,387 MiB of physical
memory under the 2,560 MiB cap. The guard cleaned all owned children.
All 29 new roots passed direct axiom checks. They use only the three allowed
axioms. The inventory now has 14,304 roots. It retains all 14,275 previous
roots. No native source artifact, table or packed-checker pilot changed.

Theta/rho still needs source membership for its byte-XOR and split-XOR
arithmetic regions. Parity real-row membership also remains open. The
original source strings still need their byte-equal bindings. FullUnsigned
is not yet proved. Design items 2 and 3 follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned theta/rho byte-XOR source obligation

The complete byte-XOR source region is closed. All 65,536 rows match the
original native literal-tree reference in all nine fields. Direct block
rules prove both byte keys, the five zero fields and the tag. The output
proof checks every physical source block. It preserves the complete XOR
operation. The membership wrapper keeps parsing and all row values explicit.

One combined output check exceeded the physical memory cap. The final
proof uses 32 bounded checks with the same proved Boolean checker. Each
check covers at most 2,048 rows. An append theorem preserves their absolute
row offsets. The output module passed in 73 seconds. It used 1,605 MiB of
physical memory. The membership wrapper passed in four seconds. It used
418 MiB. Each guard cleaned all owned children. No limit increased. No
native source artifact, table or packed-checker pilot changed. All 12 new
roots passed direct axiom checks. They use only the three allowed axioms.
The inventory now has 14,316 roots. It retains all 14,304 previous roots.

Theta/rho now needs only its split-XOR arithmetic source region. Parity
real-row membership remains open. The original source strings still need
their byte-equal bindings. FullUnsigned is not yet proved. Design items 2
and 3 follow the machine targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned theta/rho split source key obligations

The split arithmetic source keys and fixed fields are closed. The three
keys equal the original native keys on all 524,288 rows. The three unused
fields stay zero. The source tag stays 58. Exact source block windows
preserve the 65,536-row physical offset. Short periodic and constant-block
proofs then supply every row value.

The focused group passed in eight seconds. It used 715 MiB of physical
memory. The guard cleaned all owned children. No native source artifact,
table or packed-checker pilot changed. All seven new roots passed direct
axiom checks. They use only the three allowed axioms. The inventory now
has 14,323 roots. It retains all 14,316 previous roots.

Theta/rho now needs its two split output-fragment correspondences. Its
other source cases are closed. Parity real-row membership remains open.
The original source strings still need their byte-equal bindings.
FullUnsigned is not yet proved. Design items 2 and 3 follow the machine
targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned theta/rho source fragment for shift zero

The low output fragment for shift zero is closed. It reuses the complete
proved byte-XOR source column. The proof keeps the two distinct leading
blocks. The remaining 897 blocks have equal source-node indices. A general
decoder theorem supplies their equality without evaluation of the payloads.
The exact retained index window has a kernel-checked scalar certificate.

Direct block-list conversion exceeded the physical memory cap. The final
proof uses the existing checked source-decoder callbacks. It passed in six
seconds. It used 929 MiB of physical memory. All guards cleaned their owned
children. No limit increased. The index-certificate syntax now uses distinct
keywords. Both existing chi cycle certificates passed focused builds with
that syntax. Their public names and statements stay intact. Nine new and
18 retained roots passed direct axiom checks. They use only the three
allowed axioms. The inventory now has 14,332 roots. It retains all 14,323
previous roots.

The other seven low-fragment shift cases and the high output fragment stay
open. The other theta/rho source cases are closed. Parity real-row membership
also remains open. The original source strings still need their byte-equal
bindings. A direct theta string-conversion probe exceeded the memory cap.
Its failed proof was not adopted. FullUnsigned is not yet proved. Design
items 2 and 3 follow the machine targets. The packed-checker pilot stays
unchanged.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned theta/rho low source fragments for shifts two through five

Four more low output cases are closed. Each case covers all 65,536 source
rows and equals its original native low-fragment value. Exact source suffixes
bind their stored templates. The original parse premise supplies complete
column coverage. Short cycle and template rules then supply every row value.

The largest template check exceeded the physical memory cap. Eight bounded
checks now cover its 4,096 template cells. The final focused group passed in
eleven seconds. It used 752 MiB of physical memory. The guard cleaned every
owned child. No limit increased. The native artifacts and the packed-checker
pilot stay intact. All 22 new roots passed direct axiom checks. They use
only the three allowed axioms. The inventory now has 14,354 roots. It
retains all 14,332 previous roots.

The low source fragment still needs shifts one, six and seven. The high
source fragment remains open. Other theta/rho source cases are closed.
Parity real-row membership and the original source-string bindings remain
open. FullUnsigned is not yet proved. Design items 2 and 3 follow the targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned theta/rho low source fragments for shifts six and seven

Both cases are closed. Each source fragment equals its original native value
on all 65,536 rows. One periodic template supplies each case. List-based
source templates keep the equality check bounded. The original parse premise
supplies the complete source coverage.

The focused group passed in six seconds. It used 465 MiB of physical memory.
The guard cleaned all owned children. The native artifacts and the packed
checker pilot stay intact. All ten new roots passed direct axiom checks.
They use only the three allowed axioms. The inventory has 14,364 roots.
It retains all 14,354 previous roots.

Shift one is the last open low-fragment source case. The high fragment,
parity real-row membership and the original source-string bindings remain
open. FullUnsigned is not yet proved. Design items 2 and 3 follow the targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned theta/rho complete low fragments and zero overflow

The last low-fragment case is closed. One exact 32,768-row source cycle
covers both halves of the shift-one region. Sixteen bounded kernel checks
prove that cycle. All eight low source fragments now equal their original
native values. The shift-zero high fragment is also closed. All seven new
roots passed direct axiom checks. They use only the three allowed axioms.
The inventory has 14,371 roots. It retains all 14,364 previous roots.

The focused group passed in 24 seconds. It used 948 MiB of physical memory.
The guard cleaned all owned children. No limit increased. The native artifacts
and the packed checker pilot stay intact.

The other seven high-fragment cases remain open. Parity real-row membership
and the original source-string bindings also remain open. FullUnsigned is
not yet proved. Design items 2 and 3 follow the targets.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned theta/rho overflow for shifts three through six

Four more source overflow cases are closed. Direct source-template selection
proves all 65,536 rows in each case. The results equal the complete original
native values. No finite full-region row enumeration is required.

The focused group passed in 19 seconds. It used 738 MiB of physical memory.
The guard cleaned all owned children. All nine new roots passed direct axiom
checks. They use only the three allowed axioms. The inventory has 14,380
roots. It retains all 14,371 previous roots.

Overflow cases one, two and seven remain open. Parity real-row membership
and original source-string bindings remain open. FullUnsigned is not yet
proved. Design items 2 and 3 follow the targets. The packed checker pilot
stays intact.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned theta/rho source membership

Complete represented-source membership is closed for theta/rho. The final
three overflow cases equal their original native values. Exact constant
trimming and scaled blocks prove shifts one and two. Thirty-two bounded
kernel checks prove shift seven. All eight low and high output cases now
compose with the source keys, padding fields, tags, control rows and slots.

The new `split_theta_real_rows` theorem proves all 590,066 real rows. The
new `theta_source_rows` theorem also includes the proved physical padding.
The original parse and row-value premises stay explicit. No source-membership
assumption is added. The original raw source string still needs its equality
with the represented source. This binding remains open.

The final three overflow modules passed focused kernel checks. Their group
used 1,362 MiB of physical memory. The final assembly passed in four seconds
and used 429 MiB. Each guard cleaned all owned children. All sixteen new
roots passed direct axiom checks. They use only the three allowed axioms.
The inventory has 14,396 roots. It retains all 14,380 previous roots.

Parity real-row membership and all three original source-string bindings
remain open. FullUnsigned is not yet proved. Design items 2 and 3 follow
the machine targets. The native artifacts and packed checker pilot stay intact.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned parity byte-iota, slots and control source rows

All 65,536 byte-iota source rows now equal the original native rows. Both
122-row control regions also have canonical membership. A proved source-index
prefix rule retains the exact blocks from all eight stored source columns.
It avoids the large XOR-five source suffix. Every proposed prefix and scalar
witness enters an ordinary kernel proof.

The complete finite control check exceeded the physical memory cap. Eight
bounded checks now prove the same row statement. The final focused group
passed in 31 seconds. It used 1,034 MiB of physical memory. The guard cleaned
all owned children. No limit increased. All twenty-four new roots passed
direct axiom checks. They use only the three allowed axioms. The inventory
has 14,420 roots. It retains all 14,396 previous roots.

Parity XOR-five source membership and all three original source-string
bindings remain open. FullUnsigned is not yet proved. Design items 2 and 3
follow the machine targets. The native artifacts and packed checker pilot
stay intact.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned parity XOR-five source inputs and fixed fields

All five source keys now equal their original native base-sixteen digits on
all 1,048,576 arithmetic rows. Direct periodic and constant-block rules prove
these values. The complete source padding field is zero. The complete tag
field is 64. Both fixed fields equal their original native values.

The focused module passed in four seconds. It used 428 MiB of physical memory.
The guard cleaned all owned children. All five new roots passed direct axiom
checks. They use only the three allowed axioms. The inventory has 14,425
roots. It retains all 14,420 previous roots.

Only the source output field remains for parity XOR-five membership. All
three original source-string bindings remain open. FullUnsigned is not yet
proved. Design items 2 and 3 follow the targets. The native artifacts and
packed checker pilot stay intact.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned complete parity source membership

The parity source-row obligation is closed. All 1,048,576 XOR-five source
outputs equal their original native values. The other seven fields were
already proved. The new `split_parity_real_rows` theorem covers every real
parity source row. The new `parity_source_rows` theorem also includes padding.

A balanced scalar partition retains all 106,187 original block indices.
Every split enters an ordinary kernel proof. Sixty-five bounded intervals
cover the output rows after the initial zero row. Each interval has at most
16,384 rows. Seventeen modules hold these checks. Generic block rules join
their results. The initial overlapping zero row is proved separately. No
source-membership assumption is added. The packed checker pilot stays intact.

The partition passed in four seconds and used 309 MiB of physical memory.
The first interval group passed in 23 seconds. The remaining groups passed
in 277 seconds and used 1,246 MiB. The complete output and membership assembly
passed in 135 seconds and used 1,125 MiB. All guards cleaned their owned
children. No resource cap increased. All 102 new roots passed direct axiom
checks. They use only the three allowed axioms. The inventory has 14,527
roots. It retains all 14,425 previous roots.

All three split tables now have represented-source membership proofs. Chi
membership keeps its native query-tag guard. The three original source-string
bindings remain open. FullUnsigned is not yet proved. Design items 2 and 3
follow the targets. Native artifacts, production circuits and production Rust
stay intact.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned original theta source binding

The original theta source obligation is closed. The new
`SourceCaptureThetaProofs.source_eq` theorem proves exact equality with all
909,925 characters of the original JSON. The new `theta_original_source_rows`
theorem proves row membership for that original source. The target statement
keeps its original source and premises.

The kernel checks 424 string encodings and 396 number encodings. It checks
all 3,015 stored source indices against their original packed representation.
A complete bank equality preserves every source node. The renderer uses these
proved representations. Its soundness theorem connects it to the original
source interpreter.

The final source proof uses 445 intervals. Each interval has at most 2,048
characters. The kernel checks every interval and both final empty tails.
Earlier small intervals retained too many large cursor declarations and hit
the memory guard. The larger intervals passed. No resource cap increased.
The complete source equality passed in a 200-second focused run and used
849 MiB of physical memory. That run then found a namespace error in the row
adapter. The repaired adapter passed in three seconds and used 483 MiB.

All 80 new roots passed direct axiom checks. They use only `propext`,
`Classical.choice` and `Quot.sound`. The explicit inventory has 14,607 roots.
It retains all 14,527 previous roots. Production circuits, production Rust
and imported native values stay intact.

The original parity and chi source bindings remain open. FullUnsigned is
not yet proved. Design items 2 and 3 follow the targets. The packed checker
pilot stays intact. Cached and uncached captures remain required.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned exact source-bank and token obligations

The parity and chi exact-bank and token obligations are closed. The kernel
proves each new bank equal to its original bank. It preserves all 106,187
parity source indices. It also preserves both chi index lists, with 54,535
and 6,969 entries. Each scalar partition and literal list has a kernel proof.

The kernel checks every stored string and number encoding. The selector
proofs cover all indices, including the default branch. These results supply
the bank and token premises of the original-source renderer. They add no
premise to the machine target.

The four modules passed a focused build in 93 seconds. Peak physical memory
was 1,960 MiB. All 2,650 new roots passed direct axiom checks in five seconds.
They use only the three allowed axioms. The explicit inventory has 17,257
roots. It retains all 14,607 prior roots. Each guard cleaned its owned children.

The original parity and chi string bindings remain open. FullUnsigned is
not yet proved. Whole-literal parity comparisons reached a kernel recursion
limit. Separate data builds passed. The complete literal model did not pass.
Earlier diagnostic tools and failed literal representations remain outside
the repository. They supply no proof or validation result. No resource cap increased.

Design items 2 and 3 follow the targets. The packed checker pilot stays intact.
Production circuits, production Rust and native imported values stay intact.
Cached and uncached captures remain required.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned original-literal model obligations

The parity and chi literal-model obligations are closed. The kernel proves
`SourceCaptureParityLiteral.literal_checked` and
`SourceCaptureChiLiteral.literal_checked`. These proofs bind all 6,307,780
parity characters and all 4,762,907 chi characters to the original JSON strings.
They add no premise to the machine target.

Each model has checked character segments and a balanced function tree.
The kernel proves each tree join and the complete original-literal model.
The data group passed in 46 seconds. Peak physical memory was 1,768 MiB.
Both complete models passed in six seconds. Peak physical memory was
2,035 MiB. The models used a 2 GiB virtual Lean thread stack. The library
now selects that stack. The 2,560 MiB physical-memory and 5,120 MiB
bounded-resident caps stay the same.

All 11 new public roots passed direct axiom checks in two seconds.
They use only the three allowed axioms. The explicit inventory has 17,268
roots. It retains all 17,257 prior roots. Each guard cleaned its owned children.

The original parity and chi renderer equalities remain open. FullUnsigned
is not yet proved. An earlier chi interval check hit the physical-memory cap.
A narrow diagnostic found matching characters at the slow interval. An uncommitted direct-fold renderer and its soundness proofs passed
focused checks in the working tree. Its byte certificates also passed.
The complete renderer equality remains under test.

Design items 2 and 3 follow the targets. The packed checker pilot stays intact.
Production circuits, production Rust and native imported values stay intact.
Cached and uncached captures remain required.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run. The separate replay stack has
not qualified these new literal proofs.


### Full unsigned original chi source obligation

The original chi source obligation is closed.
`SourceCaptureChiProofs.source_eq` proves exact equality with all 4,762,907
characters of the original JSON. `chi_original_source_rows` supplies the
original-source row obligation of the FullUnsigned target. It retains the
native query-tag guard. The target keeps its statement and premises.

The renderer now uses primitive list folds. Its soundness proofs preserve
the original source interpreter. The new interval proof checks a finite
prefix and its exact suffix. It joins all 582 intervals and checks both
final empty tails. This avoids the large recursion-history terms that
stopped earlier attempts. No native circuit or Rust source changed.

The renderer and all three byte-certificate modules passed focused checks
in 71 seconds. Peak physical memory was 380 MiB. The complete chi character
proof passed in 881 seconds. Peak physical memory was 696 MiB. The original
chi adapter and refreshed theta binding passed in a 205-second group.
That group used at most 854 MiB of physical memory. All guards kept the
same physical-memory, resident-memory and time caps. They cleaned their
owned children.

All 17 focused roots passed direct axiom checks in three seconds. This
includes the new chi roots, the changed renderer and the existing theta
adapter. The proofs use only the three allowed axioms. The explicit
inventory has 17,271 roots. It retains all 17,268 prior roots.

The original parity source binding remains open. FullUnsigned is not yet
proved. Design items 2 and 3 follow the targets. The packed checker pilot
stays intact. Cached and uncached captures remain required.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Full unsigned target proof

`MachineTargets.Proofs.unrolled_full_soundness` proves the exact
`UnrolledFullUnsigned` target. It closes the last original-source obligation.
All three machine targets now have kernel proofs. No target statement,
reference or premise changed.

`SourceCaptureParityProofs.source_eq` proves exact equality with all
6,307,780 original parity source characters. `parity_original_source_rows`
supplies the native original-source row obligation. A primitive interval
fold checks all 385 complete intervals. The proof checks both final tails.
It preserves the complete original bank and every token encoding.

The parity character proof passed in 485 seconds. Peak physical memory
was 797 MiB. The adapter for the original source and the complete target passed in a
focused group in 12 seconds. That group used at most 558 MiB of physical memory.
The group reused the freshly checked chi and theta bindings. All guards
kept the same physical-memory, resident-memory and time caps. They cleaned
their owned children.

All 18 focused roots passed direct axiom checks in three seconds. This
includes the complete FullUnsigned target. The proofs use only `propext`,
`Classical.choice` and `Quot.sound`. The explicit inventory has 17,275 roots.
It retains all 17,271 prior roots and all established audit roots.

Production circuits, production Rust and imported native values stay intact.
Exact lookup, request and RAM matching remain explicit. Cached and uncached
captures remain required. The target admits the blessed split Keccak path.
It keeps the public special5 exclusion.

The remaining implementation work covers design items 2 and 3. This includes
the legacy compiler interfaces, capture checks that depend on the program
and the verified checker rollout. The hourly follow-up remains active.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run. Independent replay has not
qualified the new literal proofs under its separate stack setting.


### Program parameter migration: exact lookup partition

Design item 2 now has a generic exact lookup partition.
`LookupArgument.restrictTo` selects table rows and requests with the same
tuple predicate. It preserves the original natural multiplicity for each
retained row. `LookupArgument.splitBy` derives both parts of a setup split
from the original exact permutation. Neither operation assumes extra query
membership or a new matching argument.

The generic module passed a focused kernel check in two seconds. Peak
physical memory was 227 MiB. Both new roots passed direct axiom checks in
one second. They use only the three allowed axioms. The explicit inventory
has 17,277 roots. It retains all 17,275 prior roots.

The native bindings must still identify the partition predicate and each
program region. The legacy compiler interfaces still use the retained image
and decoder tables. Their migration remains open. The production OS binary
comparison and verified checker rollout also remain open.

No native circuit, Rust source or imported value changed. Exact lookup and
RAM assumptions stay explicit. Cached and uncached captures remain required.
Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Program parameter migration: native lookup row parameters

All 14 CPU profiles now define `LookupArgumentsWith`. Each definition takes
independently supplied setup rows and matches the same emitted native tuples.
The calling boundary must bind those rows to public text and fixed setup data.
Every profile also proves `lookup_arguments_with_retained` by kernel reflexivity.
This specialization gives exactly its existing lookup argument type.

All 14 original `LookupArguments` definitions keep identical source text.
The native operands, masks, setup columns and imported values stay intact.
Cached and uncached profiles both remain required.

The 14 imports, their 14 row-composition consumers and the import barrel
passed focused kernel checks in 72 seconds. Peak physical memory was
454 MiB. The group reused the unchanged finite-table cache. All 28 new
roots passed direct axiom checks in four seconds. They use only the three
allowed axioms. The explicit inventory has 17,305 roots. It retains all
17,277 prior roots. The guards cleaned all owned children.

The generator freshness check passed for all 14 profiles. Its existing
mutation test also passed. It detects drift in each complete setup binding.

The next steps bind the variable rows to each native program region and
port the legacy compiler execution interfaces. Their retained-image and
retained-decoder limits remain open. The production OS binary comparison
and verified checker rollout also remain open.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Program parameter migration: row certificates

The new `ProgramLookupRows` parameter supplies setup tuples by configuration,
lookup group and native row. Both compiler registries now define
`ProgramLogicalRowCertificate` with these rows. All 14 CPU constructors retain
their actual native input and exact lookup matching. They select the correct
circuit and cache configuration. The original certificate types stay intact.

Each registry proves `ProgramLogicalRowCertificate.row_active`. The proof
uses the physical native input. It needs no table interpretation premise.
The interface and active-bit proofs passed focused kernel checks. The final
proof group passed in eight seconds and reused the freshly checked interface.
Peak physical memory was 459 MiB. No heartbeat override was needed.

All 21 new roots passed direct axiom checks in three seconds. They include
every new CPU constructor. They use only the three allowed axioms. The
explicit inventory has 17,326 roots. It retains all 17,305 prior roots.
The guards cleaned their owned children. Generator freshness and the
existing mutation control both passed.

The native program-region bindings and execution adapters remain open.
The legacy compiler interfaces still have their retained-image and decoder
limits. The production OS binary comparison and verified checker rollout
also remain open. Exact lookup and RAM assumptions stay explicit.
Cached and uncached captures remain required.

Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Program parameter migration: source query membership

Every CPU profile now proves `source_member_with`. Exact native matching
and the existing arithmetic operand transport derive membership for each
enabled source tuple in the supplied setup rows. Both parameterized row
registries expose this result as `ProgramLogicalRowCertificate.source_member`.
They retain a finite index bounded by the actual native lookup length.
The configuration and lookup length follow from the actual row constructor.

The 14 case modules, their import barrel and both parameterized row modules
passed focused kernel checks in 50 seconds. Peak physical memory was
463 MiB. All 22 new roots passed direct axiom checks in four seconds.
They use only the three allowed axioms. The explicit inventory has 17,348
roots. It retains all 17,326 prior roots. The guards cleaned their owned
children. Generator freshness and the existing mutation control passed.

The setup interpretation is still separate. The next steps bind the rows
to the native decoder and ROM regions, then port execution acceptance.
No new decoded instruction, helper bound or expected operand is assumed.
The legacy compiler migration, production OS binary comparison and verified
checker rollout remain open. Cached and uncached captures remain required.

No native circuit, Rust source or imported value changed. Exact lookup and
RAM assumptions stay explicit. Full frontend validation, environment audit,
baseline refresh, transitive replay and Linux qualification did not run.

### Program parameter migration: native setup rows

The native setup row factory now takes decoder rows and a ROM word function.
It keeps the captured range and timestamp groups. It keeps fixed generic
rows and replaces rows selected by the decoder and ROM tags. The row model
keeps every payload field when it adds padding and a tag.

All 14 CPU profiles use geometry from the native setup exports. Kernel
proofs check their widths, decoder capacity, region bounds and ROM bounds.
Both cache modes remain required. The setup row laws, generated geometry,
row interfaces and direct consumers passed focused checks. The last group
passed in six seconds. Peak physical memory was 429 MiB. The 25 new roots
passed direct axiom checks in six seconds. They use only the three allowed
axioms. The explicit inventory has 17,373 roots. It retains all 17,348 prior
roots. Generator freshness and the existing mutation control passed. Each
guard cleaned its owned children.

The active decoder and ROM query bindings remain open. The public setup
adapter and legacy execution interfaces must use these bindings next.
The production OS binary comparison and verified checker rollout also
remain open. No native circuit, Rust source or imported value changed.
Full frontend validation, environment audit, baseline refresh, transitive
replay and Linux qualification did not run.


### Program parameter migration: native decoder adapters

All 14 CPU profiles now prove the native decoder tuple and its active weight.
Their proofs use native arithmetic and the imported decoder expressions.
Each profile then derives public decoder membership from its exact lookup
argument. Both row registries expose this result. Their trace wrappers derive
`UnrolledDecoderExactLookup` and `UnifiedDecoderExactLookup` from the actual
row certificates. Native state and constraint proofs must supply the PC range.
The adapters assume no decoded instruction or retained decoder equality.

All 28 case modules passed focused kernel checks in 72 seconds. Peak physical
memory was 451 MiB. The registry and trace wrappers passed in four seconds.
All 60 new roots passed direct axiom checks in three seconds. They use only
the three allowed axioms. The inventory has 17,459 roots. It retains all
17,399 prior roots. Generator freshness and mutation controls passed. The
controls reject changes to each lookup binding and each native decoder tuple.
Each guard cleaned its owned children.

ROM constraint transport and the legacy compiler execution migration remain
open. These must also derive the PC range from native acceptance. The
production OS binary comparison and verified checker rollout remain open.
Both cache modes remain required. No native circuit, Rust source or imported
value changed. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.


### Program parameter migration: fixed lookup bounds

All 14 CPU profiles now derive range and timestamp membership against the
unchanged native setup groups. Each profile also derives its physical helper
bounds from exact matching. The program decoder rows and ROM word function
remain parameters. The proofs assume no helper value or canonical borrow.

All 14 modules passed focused kernel checks in 37 seconds. Peak physical
memory was 457 MiB. All 42 new roots passed direct axiom checks. They use only
the three allowed axioms. The inventory has 17,501 roots. It retains all
17,459 prior roots. Generator freshness and mutation controls passed. Each
guard cleaned its owned children.

The next step transports native constraints with the program-dependent ROM
rows. The legacy execution interfaces, production OS binary comparison and
verified checker rollout remain open. Both cache modes remain required.
No native circuit, Rust source or imported value changed. Full frontend
validation, environment audit, baseline refresh, transitive replay and Linux
qualification did not run.


### Program parameter migration: ADD/SUB native constraints

ADD/SUB now proves its complete native row constraints with decoder rows
and the ROM word function as parameters. Both cache modes derive every
range and timestamp lookup from exact matching. The result holds for any
pooled setup. It needs no retained image or decoder equality.

The two modules passed focused kernel checks in ten seconds. Peak physical
memory was 436 MiB. Both public roots passed direct axiom checks with only
the three allowed axioms. The inventory has 17,503 roots. It retains all
17,501 prior roots. Generator freshness and mutation controls passed. Each
guard cleaned its owned children.

The other native CPU constraint adapters remain open. They need fixed helper
and ROM lookup transport. The legacy execution interfaces, production OS
binary comparison and verified checker rollout also remain open. Both cache
modes remain required. Full frontend validation, environment audit, baseline
refresh, transitive replay and Linux qualification did not run.


### Program parameter migration: fixed helper CPU constraints

Jump/Branch and MUL/DIV now prove their complete native row constraints
with program setup rows as parameters. Both cache modes derive fixed helper
membership from exact matching. Kernel proofs check the helper tags against
zero, decoder and ROM tags. The result holds for any pooled setup. It needs
no retained image or decoder equality. Together with ADD/SUB, six of the
14 CPU profiles now have this constraint adapter.

The fixed helper membership lemmas also cover Shift/Binop. Its constraint
adapter still needs a native arithmetic proof for the variable helper tags.
The failed prototype stays outside the repository. It added no premise.
The completed statements and references stay unchanged.

All six native constraint adapters passed focused kernel checks. The last
61-module group passed in 18 seconds. It reused modules from the preceding
focused passes. Peak physical memory was 458 MiB. All ten new public roots
passed direct axiom checks with only the three allowed axioms. The inventory
has 17,513 roots. It retains all 17,503 prior roots. Generator freshness and
mutation controls passed. Each guard cleaned its owned children.

Shift/Binop, subword, word-memory and unified constraint adapters remain
open. They need variable helper tag or ROM transport. The legacy execution
interfaces, production OS binary comparison and verified checker rollout
also remain open. Both cache modes remain required. No native circuit, Rust
source or imported value changed. Full frontend validation, environment
audit, baseline refresh, transitive replay and Linux qualification did not run.


### Program parameter migration: native decoder PC bounds

All 14 CPU profiles now prove the outgoing PC low-limb bound from native
range matching and arithmetic. These proofs do not use decoder membership.
Both row registries transfer the bounds through exact state matching.
The public initial PC bound then gives the range of every incoming decoder
query. The trace adapters derive public decoder matching without a per-row
typing premise or complete helper-table constraint adapter.

Every case module and both trace adapters passed focused kernel checks.
The last 76-module group passed in four seconds. It reused the freshly
checked case modules. Peak physical memory was 474 MiB. All 20 new roots
passed direct axiom checks with only the three allowed axioms. The inventory
has 17,533 roots. It retains all 17,513 prior roots. Generator freshness and
mutation controls passed. Each guard cleaned its owned children.

The next step uses public decoder data to constrain variable helper tags.
Native constraint transport remains open for Shift/Binop, subword,
word-memory and unified rows. The legacy execution interfaces, production
OS binary comparison and verified checker rollout also remain open. Both
cache modes remain required. No native circuit, Rust source or imported
value changed. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.

### Program parameter migration: Shift/Binop constraints

Both Shift/Binop cache modes now prove their complete native row constraints
for the public program setup. Native assertions bind the five helper tags
to the selector bits. Public decoder matching fixes the selector and operation
cases. These facts exclude the decoder, ROM and zero tags. Exact matching
then transports each request to the fixed helper table. The proof derives
all tag conditions. It adds no tag premise. The incoming PC bound comes
from the existing exact state-matching adapter.

The public tag proof and both native constraint adapters passed focused
kernel checks. The last group passed in seven seconds. Peak physical memory
was 462 MiB. All 11 new public roots passed direct axiom checks with only
the three allowed axioms. The inventory has 17,544 roots. It retains all
17,533 prior roots. Generator freshness and mutation controls passed.
Each guard cleaned its owned children.

Eight of the 14 native CPU constraint adapters are complete. Subword,
word-memory and unified rows remain open in both cache modes. The legacy
execution interfaces, production OS binary comparison and verified checker
rollout also remain open. No native circuit, Rust source or imported value
changed. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.

### Program parameter migration: subword ROM constraints

The subword setup has two program-dependent ROM regions. Their tags are 44
and 45. The new program row factory includes both regions. It uses the public
ROM word function and the imported fixed load tables. It keeps the exact
native decoder bounds, zero padding, range group and timestamp group.
It preserves the earlier basic row factory and all its public declarations.

Both subword cache modes now prove their complete native row constraints
with this program row factory. Native arithmetic excludes the decoder tag
from each helper request. Exact matching then supplies a public table row.
The proof needs no retained image or expected helper value. Ten of the
14 CPU profiles now have program-parameter constraint theorems.

The new factory, query interpretation, arithmetic guard and both native
constraint adapters passed focused kernel checks. The last group passed
in six seconds. Peak physical memory was 452 MiB. All ten new public roots
passed direct axiom checks with only the three allowed axioms. The inventory
has 17,554 roots. It retains all 17,544 prior roots. Generator freshness and
mutation controls passed. Each guard cleaned its owned children.

The new subword factory still needs decoder and PC registry integration.
Word-memory and unified constraint adapters remain open in both cache modes.
The legacy execution interfaces, production OS binary comparison and verified
checker rollout also remain open. No native circuit, Rust source or imported
value changed. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.

### Program parameter migration: complete unrolled row registry

The unrolled row registry now uses the complete public program factory.
Both subword cache modes derive decoder membership from that factory.
The proof excludes fixed helper and ROM rows from the decoder tag. It also
rejects decoder padding through the incoming PC bound. Native range matching
and exact state matching supply that bound for every row.

All 12 unrolled CPU profiles now derive exact public decoder matching
with this factory. The trace adapter needs the public setup, native row
certificates, exact state matching and the public initial PC bound.
It adds no per-row PC or decoded-instruction premise.

The decoder interpretation, both subword adapters and complete unrolled
registry passed focused kernel checks. The last group passed in ten seconds.
Peak physical memory was 479 MiB. All 13 new public roots passed direct
axiom checks with only the three allowed axioms. The inventory has 17,567
roots. It retains all 17,554 prior roots. Generator freshness and mutation
controls passed. Each guard cleaned its owned children.

Word-memory and unified constraint adapters remain open in both cache modes.
The legacy execution interfaces, production OS binary comparison and verified
checker rollout also remain open. No native circuit, Rust source or imported
value changed. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.

### Program parameter migration: complete unrolled row constraints

Both word-memory cache modes now prove their complete native row constraints
for the public initial image. Each native ROM query is zero or reads the
public word function. Successful initial-image construction and explicit ROM
coverage bind that word to the public ROM table. The proof needs no retained
program image. Native arithmetic supplies the decoder-tag exclusion.

The unrolled registry now derives constraints for all 12 CPU profiles against
the public ROM and subword tables. Its trace adapter derives each incoming
PC bound from native ranges and exact state matching. It adds no per-row PC,
helper-tag or expected-value premise. Decoder matching remains explicit.

The new query interpretation, arithmetic guard, both word-memory adapters
and complete constraint registry passed focused kernel checks. The final
registry group passed in five seconds. Peak physical memory was 479 MiB.
All 12 new public roots passed direct axiom checks with only the three allowed
axioms. The inventory has 17,579 roots. It retains all 17,567 prior roots.
Generator freshness and mutation controls passed. Each guard cleaned its
owned children.

Native constraint transport remains open for the two unified profiles.
The legacy execution interfaces, production OS binary comparison and verified
checker rollout also remain open. No native circuit, Rust source or imported
value changed. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.

### Program parameter migration: complete unified row constraints

Both unified cache modes now prove their complete native row constraints
for the public program setup. Public decoding fixes the operation tag.
Arithmetic assertions derive the dispatcher bound and all five helper tags.
Exact matching supplies fixed helper rows or public ROM words. The result
needs no retained program image or expected helper value.

The unified trace adapter derives every incoming PC bound from native ranges
and exact state matching. All 14 CPU profiles now have public program
constraint adapters. Both row registries compose these adapters without a
per-row PC, operation-tag or expected-value premise.

The decoder guard, arithmetic guards, ROM interpretation, both native
adapters and unified registry passed focused kernel checks. The arithmetic
guard group took 40 seconds. Peak physical memory was 845 MiB. The final
native-adapter group took 13 seconds. The registry group took four seconds.
All 13 new public roots and the retained dispatcher root passed direct axiom
checks with only the three allowed axioms. The dispatcher theorem keeps its
public name and statement. Its shared proof moved to the arithmetic module.
The inventory has 17,592 roots. It retains all 17,579 prior roots. Generator
freshness and mutation controls passed. Each guard cleaned its owned children.

The legacy execution interfaces, production OS binary comparison and verified
checker rollout remain open. No native circuit, Rust source or imported value
changed. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.

### Program parameter migration: native machine acceptance

The native acceptance adapter now closes the CPU-equation, execute and decoder
matching premises for all three machine targets. It uses the public program
setup and physical row certificates. The unrolled adapter retains explicit ROM
coverage and initial-image construction. Worker equations and exact state,
request and RAM matching keep the same meaning.

Both new modules passed focused kernel checks in four seconds. Peak physical
memory was 525 MiB. All four new roots passed direct axiom checks with only the
three allowed axioms. The inventory has 17,596 roots. It retains all 17,592 prior
roots. Generator freshness and mutation controls passed. Both guards cleaned
their owned children.

The legacy execution interfaces, production OS binary comparison and verified
checker rollout remain open. No native circuit, Rust source or imported value
changed. Full frontend validation, environment audit, baseline refresh,
transitive replay and Linux qualification did not run.

### Program parameter migration: Review compatibility cleanup

The three machine targets remain the canonical Review API. Earlier captured
program, image and execution declarations now live in the compatibility proof
layer. The original paths forward to that layer. All ten moved declaration
bodies have identical hashes. Each public name and statement stays the same.
No Review statement refers to the retained program or imported-image premise.

Public split schedule and complete-call reference definitions now live in the
helper layer. This removes five high-level trace imports from circuit and
helper modules. Their definitions and imported values stay the same. The source
layer check passes with the same three established assembly exceptions.

The focused source group passed for 55 modules in 91 seconds. It refreshed stale
legacy decoder objects and reused unchanged finite-table checks. Peak physical
memory was 594 MiB. All 28 moved public declarations passed direct axiom checks
with only the three allowed axioms. All 17,596 explicit roots remain unchanged.
The guide check passed for 1,324 links. Both successful guards cleaned their
owned children. Earlier cache-repair failures also cleaned their owned children.

The public native adapter still imports legacy decoder proofs through shared
transport and ROM modules. That dependency cleanup, production OS differential
coverage and checker rollout remain open. Full frontend validation, environment
audit, baseline refresh, transitive replay and Linux qualification did not run.

### Program parameter migration: independent public proof graph

The native public-program adapter no longer imports decoder-tail proofs,
per-capture decoder interpretation or retained-image contracts. Generic tuple
transport now lives in one module per CPU profile. The original logical-row
modules retain their captured-program corollaries and public names. Generic
stateful program construction and ROM row facts also have independent modules.
The native word padding proof reads the last fixed blocks directly. It does
not use captured decoder-row interpretation. No premise or conclusion changed.

The source guard checks all 2,773 modules in the public acceptance graph. It
rejects captured decoder or compatibility imports. A mutation that adds an
actual decoder-tail dependency was rejected. Review source and layer scans pass.
All 17,596 explicit audit roots remain unchanged.

The focused source group passed for 113 modules. This group includes every
changed transport, its program adapters and native acceptance ancestors. It
retains the unchanged finite-table cache. The final increment took eight
seconds. Peak physical memory across the source groups was 559 MiB. All 157
moved public transport and ROM declarations passed direct axiom checks with
only the three allowed axioms. Generator freshness and both mutation families
passed. Each guard cleaned its owned children.

The production OS differential and verified checker rollout remain open. Full
frontend validation, environment audit, baseline refresh, transitive replay and
Linux qualification did not run.

### Program parameter migration: stateful decoding and public OS differential

Public decoding now runs the original Sail decoder in the public initial state.
The decoder can read misa for M-extension words. A kernel theorem proves that
successful decoding preserves that state. The public program constructors and
their source, image and initialization proofs use this result. No expected
decoder result or state-frame premise was added.

The public OS comparison found the earlier pure-only decoder error at word 38,
`0x02e585b3` (MUL). The native decoder row was correct. The repaired Lean model
now agrees with all 14 full and unified OS exports in both cache modes. The
[pinned fixture](artifacts/programs/README.md) records the public release, commit,
asset sizes and hashes. The fetcher rejects a changed cached asset. CI requires
the OS comparisons and the new MUL/DIV regression. The OS uses special5 calls.
These comparisons do not prove OS execution under the machine targets.

The focused source group passed for 205 modules in 724 seconds. Peak physical
memory was 2,388 MiB. The group includes all 14 native CPU adapters, acceptance
and all three machine target proofs. Exact target-type checks passed. The three
targets and three new decoder roots passed direct axiom checks with only the
three allowed axioms. The inventory has 17,599 roots. It retains all 17,596 prior
roots. The public acceptance graph has 2,774 modules and passes its source guard.

The current native oracle recompiled six changed leaf modules and linked the
retained package-qualified native objects. Its build record hashes all 1,826
link inputs. This check explicitly trusts the retained native dependency cache.
The relink took 34 seconds. Peak physical memory was 919 MiB. A separate fresh
source check rebuilt the unchanged ROM-byte data object in 144 seconds. The
normal dependency-refresh build reached its 900-second guard. It did not finish.
No full executable freshness pass is claimed.

The public OS differential passed in 213 seconds. Peak physical memory was
2,229 MiB. All 22 new MUL/DIV comparisons and 21 committed verifier comparisons
passed before the combined 900-second guard expired. The last cached reduced
word-memory comparison passed in a separate run. Thus all 22 committed verifier
comparisons passed. Both cache modes remain required. Each guard cleaned its
owned children. The tests used the newly linked oracle.

Generator freshness, both native-binding mutation families and six decoder
controls passed. The guide check passed for 1,328 links. The source-layer check
retains the same three established assembly exceptions. No production circuit,
Rust source or imported value changed. Full frontend validation, normal native
executable freshness, environment audit, baseline refresh, transitive replay
and Linux qualification did not run to completion. Checker rollout remains open.

### Complete BlakeRound query frames (2026-11-01)

Both BlakeRound captures now use one complete indexed kernel check. Each capture
has 1,152 fields. A proved coordinate mask replaces repeated membership scans.
Balanced numeric trees replace repeated address-list scans. The soundness theorem
derives the original numeric checker. The original semantic finalizer remains.

Exact kernel bindings cover all five source components. They retain every field
and every term, including zero terms. The address windows contain at most 32
entries. The field windows contain at most 16 entries. A generic coverage proof
joins every window and proves the complete source equality. These windows bind
data. They do not split the semantic check.

The complete wrappers derive all old per-field and block facts from the result.
They retain the old block data and flattening theorem. The 36 old proof shards
are gone. The two captures use 20 modules, including their inputs and finalizers.
All 2,390 original public declarations remain. The kernel accepts all 2,348 old
theorem types. All 42 imported data values have identical Expr values.
The shared field-length proof also preserves the AddSub pilot. Its 36 old theorem
types pass again. Its six imported data values remain identical.

All 30 selected modules pass source checks and kernel replay. They include both
BlakeRound direct witness consumers and the changed AddSub wrappers. Each replay
uses the standard 32 MiB stack. No safe dependency is skipped. These checks trust
imported objects. All 3,232 focused axiom checks use only the three allowed axioms.
All 24 exact controls pass. The kernel rejects all 24 mutations. The legacy
finalizer passes. Both importers reject opaque payloads. Four generator controls
pass. Capture, interface and inventory freshness pass. Static checks, workflow
syntax and the source import graph pass. The inventory has 74,907 roots. It
retains all 74,065 prior roots and every established root.

The capture source and replay batch takes 388.61 s. It peaks at 2079.53 MiB.
The complete cached wrapper builds in 8.13 s and replays in 2.47 s. The uncached
wrapper builds in 8.11 s and replays in 2.53 s. Both use default heartbeats.
The two materializers use a scoped two-million heartbeat budget. The default
budget cannot erase the complete typed field list. The kernel checks each source
binding separately. The first wrapper batch repeated the field-count reduction.
One shared length theorem reduces a 64-field source check from 16.42 s to 2.21 s.
The complete wrappers replace that batch. The first axiom query omitted the two
AddSub input imports. The direct-consumer, preservation and control guard takes
290.77 s and peaks at 1036.17 MiB. The corrected query passes. The final guard
takes 5.66 s and peaks at 819.57 MiB. All guards clean their owned workers.

The flat whole check exceeds the memory cap. A slice of the complete List.ofFn
source also exceeds the cap. The adopted source windows construct only their
bounded entries. The indexed whole check builds in about 2.7 s and replays in
about 2.7 s per capture. The data-binding cost remains separate. This checkpoint
does not claim a cold full-build gain.

The other 18 query-frame captures remain open. Other frame and argument families
remain open. Full frontend validation, the environment audit and baseline refresh,
full transitive replay, cold full measurements, and Linux runtime and warm-cache
qualification remain pending for review. The known aggregate ownership collision
remains deferred. This checkpoint does not establish an aggregate import pass.

### Complete native query-frame family (2026-11-01)

All 22 cached and uncached captures now use complete query-frame checks. The
AddSub pilot keeps its original layout. The other 20 captures use the proved
indexed checker and complete source bindings. No query-frame proof shard remains.
The generator rejects shard phases for adopted captures. The original semantic
finalizers and exact premises remain.

The last 18 captures preserve all 2,236 original public declarations. The kernel
accepts all 2,170 old theorem types. All 66 imported data values have identical
Expr values. The old Keccak block data and flattening theorems remain. The last
12 old proof shards are gone. Every new capture uses default heartbeats. Only
the two previously qualified BlakeRound materializers need a scoped override.

All 198 selected modules pass source checks and kernel replay. They include all
18 direct witness consumers. Each replay uses the standard 32 MiB stack. No safe
dependency is skipped. These checks trust imported objects. All 3,592 focused
axiom checks use only the three allowed axioms. All 84 exact controls pass. The
kernel rejects all 84 mutations. The legacy finalizer passes. Both importers
reject opaque payloads. These controls cover each complete check, each coordinate
binding and the final field and placement windows. Earlier controls for AddSub
and BlakeRound remain qualified. Four generator controls pass for all 22 captures.
Capture, interface and inventory freshness pass. Static checks, workflow syntax
and the source import graph pass. The inventory has 76,263 roots. It retains all
74,907 prior roots and every established root.

The Keccak and Bigint source and replay batch takes 239.81 s. It peaks at
1150.84 MiB. The other 14 captures take 614.17 s and peak at 984.09 MiB.
Qualification takes 508.51 s and peaks at 844.81 MiB. Each guard cleans its owned
workers. The first generalized preservation script used a reserved binder name.
The corrected script passes. Each capture has a separate preservation and axiom
query. This checkpoint does not establish an aggregate import pass or a cold
full-build gain.

Other frame and argument families remain open. MemoryFrame still checks RAM,
initialization and execute fields per index. Its source-port predicate is the
next concrete family. Counter, oracle and history metadata also need a scope
check. Full frontend validation, the environment audit and baseline refresh,
full transitive replay, cold full measurements, and Linux runtime and warm-cache
qualification remain pending for review. The known aggregate ownership collision
remains deferred.

### Complete memory-frame pilot (2026-11-01)

AddSubCached and AddSubUncached now use one complete memory-frame check each.
NumericMemoryFrameChecks.check_sound derives the original RAM, initialization
and execute predicates. It keeps both erasure scopes. RAM uses activeCoordinates.
Initialization and execute use allCoordinates. It preserves the exact input-bank,
full-bank and oracle-independence tests. A proved address-code decoder handles
all original address classes. The semantic finalizers and their premises remain.

The strict importer materializes only closed natural data. Separate complete
kernel equalities bind both masks, four address maps and all three field lists.
The source binding retains every coefficient and term. The original imported
values stay in the data inputs. One result derives every old per-index fact.
All pilot modules use default heartbeats.

All 142 original public declarations remain. The kernel accepts all 130 old
theorem types. All 12 imported data values have identical Expr values. All 15
selected modules pass source checks and kernel replay. They include both direct
witness consumers. Each replay uses the standard 32 MiB stack. No safe dependency
is skipped. These checks trust imported objects. All 171 focused axiom checks use
only the three allowed axioms. All 17 exact controls pass. The kernel rejects all
17 mutations. The legacy finalizer passes. The importer rejects an opaque payload.
Three generator controls pass. Capture, interface and inventory freshness pass.
Static checks, workflow syntax and the source import graph pass.
The inventory has 76,292 roots. It retains all 76,263 prior roots.

The shared checker and importer source and replay guard takes 13.08 s and peaks
at 830.24 MiB. The capture guard takes 36.02 s and peaks at 947.04 MiB. The
finalizer guard takes 24.06 s and peaks at 835.71 MiB. Qualification takes 84.12 s
and peaks at 833.34 MiB. All guards clean their owned workers. The first finalizer
build used a reserved local name. The corrected build passes. This pilot proves
fidelity and soundness. It does not establish a cold full-build gain.

The other 20 memory-frame captures remain open. Qualify the largest captures next.
Use complete source bindings. Use bounded windows if a whole binding exceeds the
cap. Other frame and argument families remain open. Full frontend validation,
the environment audit and baseline refresh, full transitive replay, cold full
measurements, and Linux runtime and warm-cache qualification remain pending for
review. The known aggregate ownership collision remains deferred.

### Dense memory-frame scaling controls (2026-11-01)

The unadopted BlakeRoundCached probe has 616 RAM fields. Its memory bank has
771 addresses. The first 763 match the original arithmetic inputs exactly.
Default materialization stops at the heartbeat budget after 11.50 s. A scoped
two-million budget reaches the footprint cap at 2560.43 MiB. No binding runs.
A separate placement component builds in 49.44 s and replays in 1.90 s. The
full-address component alone also reaches the cap. Do not repeat these variants.

A proved prefix constructor preserves the complete original numeric capture.
It uses the actual input prefix, both bank inverse laws and the existing full-bank
input projection. All these facts have kernel proofs. The constructor changes no
reference, imported value or semantic premise. Its generic equality theorem and
the exact native prefix facts pass source checks and standard-stack replay.
The prefix capture builds in 17.77 s and replays in 1.87 s. Its whole record
binding still reaches the cap. Bounded exact windows solve that binding cost.

All four address vectors and all 616 RAM polynomials now have complete bounded
bindings in the prototype. The masks and other field lists remain fully bound.
The transport proofs unfold only their named source functions. They do not split
literal data. All ten prototype modules pass source checks and selected replay
across the successful focused runs. The final complete checker builds in 2.12 s
and replays in 2.07 s. No safe dependency is skipped. The final tail guard takes
9.65 s and peaks at 930.51 MiB. It leaves no owned worker.

These sources remain under memory-frame-large-prototype in the evidence folder.
NumericMemoryFramePrefix.lean remains there too. The prototype is not adopted.
Next generate both canonical BlakeRound modes. Run preservation, controls, axiom
checks and direct consumer checks before adoption. Keep the AddSub pilot as it is.
The other 20 memory-frame captures remain open. Full validation remains pending.

### Complete dense memory-frame captures (2026-11-01)

Both BlakeRound cache modes now use one complete numeric checker result. The
proved prefix constructor keeps the original capture exactly. Closed prefix and
bank inverse proofs justify the adapter. Complete bounded bindings cover all
four address vectors and all 616 RAM polynomials in each capture. They preserve
zero terms and term order. The masks, initialization list and execute list also
have exact bindings. The original semantic finalizers and premises remain.

The rollout retires 20 old RAM proof shards. All 1,304 old public declarations
remain. Kernel preservation accepts all 1,272 old theorem types. All 32 imported
data values are identical. All 25 selected source checks and replays pass. These
include both direct witness consumers. Replay uses the standard 32 MiB stack and
skips no safe dependency. All 2,189 focused axiom checks use only the three allowed
axioms. All 41 exact controls and 41 kernel mutation rejections pass. The legacy
finalizer and opaque-payload rejection pass. All four Python generator controls
pass. Source and interface freshness, static checks, the source import graph and
workflow syntax pass. The inventory has 77,177 roots. It retains all 76,292 prior
roots and every established root.

The canonical source and replay guard takes 267.18 s and peaks at 1,231.09 MiB.
Each whole checker builds in about 2.1 s and replays in about 2.1 s. The complete
native wrappers build in about 4.9 s and replay in about 2.1 s. These focused
measurements do not establish a cold full-build gain. The two dense materializers
use a scoped two-million heartbeat budget. All other new modules use the default
budget. The AddSub pilot outputs remain unchanged.

The first mutation run stops at a syntax error in the test expression. The
corrected run passes. The preservation and consumer results remain valid. All
guards clean their owned workers. Evidence uses memory-frame-blake-* in the
checker evidence folder. The original objects remain in
memory-frame-blake-original-oleans. The other 18 memory-frame captures remain
open. Their original objects are archived. Other frame and argument families
also remain open. Full frontend validation, the environment audit and baseline
refresh, full transitive replay, cold full measurements, and Linux runtime and
warm-cache qualification remain pending for review. The known aggregate import
collision remains deferred.

The final qualification guard takes 167.90 s and peaks at 551.90 MiB.

### Complete memory-frame rollout (2026-11-01)

All 22 memory-frame captures now use one closed numeric result per capture.
The remaining 18 captures use the proved prefix constructor and complete bounded
source bindings. The original predicates, semantic finalizers and premises stay
unchanged. RAM uses the active mask. Initialization and execute use the full
coordinate mask. Both Unified modes bind all 28 initialization fields exactly.
The rollout retires the ten old Bigint RAM proof shards. No memory-frame proof
shard remains. The AddSub and BlakeRound capture outputs remain unchanged.

The 18 captures retain all 2,280 old public declarations.
Kernel preservation accepts all 2,162 old theorem types.
All 118 imported data values are identical. All
216 selected source checks and replays pass. These
include every direct witness consumer. Replay uses the standard 32 MiB stack
and skips no safe dependency. All 4,086 focused axiom checks use
only the three allowed axioms. All 76 exact controls and 76 kernel
mutation rejections pass. These include the complete Unified initialization lists
and masks. The prior checkpoint qualifies the shared controls, legacy finalizer
and opaque-payload rejection. All four Python generator controls pass. Capture
and interface freshness, static checks, the local source import graph and workflow
syntax pass. CI keeps both modes and checks the complete family.

The inventory has 78,983 roots. It retains all
77,177 prior roots and every established root. The dense source
and replay guard takes 232.55 s and peaks at
992.95 MiB. The ordinary source and replay
guard takes 657.60 s and peaks at
884.68 MiB. Qualification takes
451.88 s and peaks at
845.03 MiB. All guards clean their
owned workers. All 18 new captures use default heartbeat limits. Only the two
BlakeRound materializers retain the documented scoped budget. No cold full-build
gain is claimed.

Evidence uses memory-frame-remaining-* in the checker evidence folder. The
30 original objects remain in memory-frame-remaining-original-oleans. Item 3
remains open. Functional graph step and base checks still use numerical proof
shards. Other frame and argument families also need migration or a scope audit.
A focused scan finds 1,130 high heartbeat settings under GKRProtocol. Do not treat
the memory-frame rollout as completion of the wider work. Full frontend
validation, the environment audit and baseline refresh, full transitive replay,
cold full measurements, and Linux runtime and warm-cache qualification remain
pending for review. The known aggregate import collision remains deferred.

### Functional-step checker scaling (2026-11-01)

The functional-step pilot remains unadopted. A typed whole-program check passes
for AddSubCached. It builds in 5.56 s and replays in 2.43 s. The same pattern
reaches the footprint cap for BlakeRoundCached at 2,565.49 MiB. Whole numeric
materialization also reaches the cap when it copies each known-address prefix.
A whole program.map port materializer reaches the cap too. Do not repeat these
variants.

The generic numeric model now has a proved balanced-set checker. It uses
Std.TreeSet Nat for the known addresses. Its soundness theorem derives the exact
original FunctionalProgram.check predicate. Both generic source and replay pass.
The list-based whole numeric check reaches the cap. The balanced-set result for
all 674 cached steps builds in 5.90 s and replays in 5.99 s. Its guard peaks at
2,291.16 MiB. No safe dependency is skipped.

Explicit 32-step port materializers fit. Late blocks exceed the default heartbeat
budget, so the prototype scopes a two-million budget to materialization. The
cached data builds in 224.93 s and replays in 1.62 s. Its guard peaks at
1,381.67 MiB. The uncached data has 394 steps. It builds in 104.57 s and replays
in 1.65 s. Mark the aggregate data noncomputable. A computable aggregate triggers
a Lean compiler IR error. This change does not change the data or the kernel
predicate. Prototype stdout progress remains buffered, even after a flush.

Thirty-two-entry bindings exceed the cap for late source windows. Direct first
window binding passes. Offset 640 with width eight also passes. Complete eight
entry bindings now pass for both modes. The cached binding builds in 208.22 s
and replays in 204.04 s. Its native program-check certificate builds in 6.37 s
and replays in 6.23 s. The combined guard peaks at 2,343.65 MiB. The uncached
binding builds in 96.64 s and replays in 92.89 s. Its certificate builds in
5.10 s and replays in 4.84 s. That guard peaks at 1,900.34 MiB. Both old
last-step theorem types also pass source and replay. All six exact controls,
six kernel mutation rejections and 23 generic axiom checks pass.

A separate untrusted export reads the closed natural port data. Literal data
for both modes passes exact kernel equality with the materialized data. These
source builds take 3.60 s and 4.00 s. Replays take about 1.52 s each. The four
literal data and preservation modules pass source and replay. Their guard peaks
at 788.35 MiB. The canonical generator must add source-hash freshness and retain
the complete original kernel bindings. Do not trust the export as a proof.

Two old cached step shards provide a focused baseline. The first 32 steps build
in 6.86 s and replay in 6.89 s. Steps 640 through 671 build in 20.40 s and replay
in 20.68 s. These samples do not establish a full-family or cold full-build gain.

All prototype sources, reports and generators remain in the checker evidence
folder. Evidence prefixes are functional-steps-*, functional-step-*, and
functional-literal-probe. Thirty-five original dense step modules remain in
functional-steps-original-oleans. All guards clean their owned workers. The
remaining adoption work is canonical literal generation, all old step theorem
corollaries, complete interface preservation, controls, CI and direct consumers.
Base-port and base-relation checks remain separate open obligations. No
functional native wrapper has changed. Item 3 and final full validation remain
open. The hourly follow-up stays active.

## Complete dense functional step captures

Both BlakeRound cache modes now use complete numeric step checks. The cached
program has 674 steps. The uncached program has 394 steps. Each capture has one
closed kernel result. A proved balanced-set checker derives the exact original
`FunctionalProgram.check`. Complete eight-entry bindings retain every input,
output, base flag and port order. The checker reconstructs the original known
address state. It adds no caller premise.

Literal data replaces repeated Meta materialization in source builds. Source
hashes bind the numeric files to the native artifact, foundation and reflector.
The strict exporter emits untrusted natural data. The kernel bindings establish
its full source fidelity. CI checks both modes, source hashes, generator output,
the native interface and mutation controls.

All 1,068 old `stepCheckedN` names remain. Their proofs select facts from the
complete result. The 35 old step proof shards are gone. All base-port and
base-relation declarations keep their original proofs. The original semantic
finalizer remains. It checks the full execution expression of a canonical value
that the foundation declares before numeric imports. This keeps the original
ring instance paths. The first preservation control found a changed instance
path in that value. The final control accepts its exact original type and value.

All 5,530 old public declarations remain. A kernel control accepts all 2,549 old
theorem types. All 2,981 old data Expr values are identical. All 19 selected
modules pass source checks and replay. These modules include both foundations,
finalizers, functional-link consumers and source-contract consumers. Replay uses
the standard 32 MiB stack. It skips no safe dependency. All 6,233 focused axiom
checks use only the three allowed axioms. Ten exact controls pass. The kernel
rejects all ten mutations. The opaque-data control and both small exporter
controls pass. All five Python generator controls pass.

The capture source and replay guard takes 812.60 s. It peaks at 2,348.12 MiB.
Cached binding source and replay take 210.09 s and 206.27 s. Its complete check
builds and replays in about 6 s. Its corollaries build in 104.61 s and replay in
14.28 s. Uncached binding source and replay take 95.70 s and 93.42 s. Its
complete check builds and replays in about 5 s. Its corollaries build in
35.79 s and replay in 6.09 s. Final qualification takes 293.52 s. It peaks at
2,255.38 MiB. Both completed guards clean their owned workers. Two intermediate
qualification restarts stop safely during the instance-path repair.

The explicit inventory has 79,633 roots. It retains all 78,983 prior roots and
every established root. Freshness, source-layer checks, static checks and
workflow syntax pass. No cold full-build gain is claimed.

Evidence prefixes are functional-steps-canonical, functional-steps-qualification4
and functional-canonical-probe in the checker evidence folder. Original objects
remain in functional-steps-complete-original-oleans. The other 20 functional step
captures remain open. All functional base checks and the other argument and
frame families remain open. Item 3 is not complete. The hourly follow-up stays
active. Full frontend validation, environment audit and baseline refresh, full
transitive replay, cold full measurements and Linux qualification did not run.
They remain pending for implementation review. The known aggregate ownership
collision stays deferred. No aggregate import pass is claimed.

## Complete functional step family

All 22 native functional step captures now use complete kernel checks. The other
20 captures reuse the qualified dense checker and exact binding pattern. Each
capture keeps one closed result. All old step facts select that result. The
remaining 62 old step shards are gone. No functional step proof shard remains.
Both cache modes stay required. The original semantic finalizer checks the full
canonical execution expression. All base-port and base-relation proofs stay
unchanged. These base checks remain a separate open family.

All 9,871 original public declarations in the remaining captures stay
available. A kernel control accepts all 4,668 old theorem types. All
5,203 old data Expr values are identical. This includes every original
canonical value. All 160 selected modules pass source checks and replay. They
include 40 direct functional-link and source-contract consumers. Replay uses
the standard 32 MiB stack. It skips no safe dependency. All 12,053 focused
axiom checks use only the three allowed axioms. Forty exact capture controls
pass. The kernel rejects all forty mutations. The shared six controls and the
opaque-data control retain their qualified dense results. All five expanded
Python generator controls pass.

The six larger source captures take 361.81 s. Their guard peaks
at 1,500.90 MiB. Their qualification takes 268.62 s and peaks
at 2,281.77 MiB. The other fourteen source captures take
319.38 s and peak at 987.37 MiB. Their qualification takes
426.13 s and peaks at 2,272.74 MiB. All guards clean their owned
workers. The untrusted export takes 203.72 s and peaks at 2,255.71 MiB. Its first
attempt lacks the object overlay and stops before materialization. The corrected
run passes. The two dense capture outputs are unchanged.

The explicit inventory has 80,755 roots. It retains all 79,633 prior
roots and every established root. Source and interface freshness, source-layer
checks, static checks and workflow syntax pass. CI checks the complete family.
No cold full-build gain is claimed. Original objects remain in
functional-steps-remaining-original-oleans. Evidence prefixes are
functional-steps-remaining-dense and functional-steps-remaining-ordinary.

Item 3 remains open. Functional base checks and other numerical argument and
frame families remain. Inspect the scope of parametric semantic proofs before
migration. Decoder interpretation and program-dependent setup stay excluded.
The hourly follow-up stays active. Full frontend validation, environment audit
and baseline refresh, full transitive replay, cold full measurements and Linux
runtime and cache qualification did not run. They remain pending for review.
The known aggregate ownership collision stays deferred. No aggregate pass is
claimed.

## Complete functional base pilot

AddSub and BlakeRound now use one complete base check per cache mode. The four
captures retain all 115 bindings. NumericFunctionalBaseChecks.check_sound
derives the exact original port and polynomial predicates. The port check keeps
every output and recipe input. It checks the full bank address round trip and
the original base classification. The polynomial check compares the original
recipe relation with the original gate.inputResidual. It keeps every term, zero
coefficient and original order. The source binds both polynomial sides and all
ports in the kernel. No caller premise changes.

All old basePortsCheckedN and baseRelationCheckedN names remain. They select
facts from the complete result. Six old base proof shards are gone. The step
captures and semantic finalizer stay unchanged. All 4,944 original public
declarations remain. A kernel control accepts all 1,677 old theorem
types. All 3,267 old data Expr values are identical. All 34 selected
modules pass source checks and replay. These include all four finalizers and
eight direct consumers. Replay uses the standard 32 MiB stack. It skips no safe
dependency. All 5,755 focused axiom checks use only the three allowed
axioms. Fourteen exact controls pass. The kernel rejects all fourteen mutations.
The opaque-payload control and three Python generator controls pass. The five
step generator controls also pass with the new base dispatch.

An eight-row whole-map binding for the largest capture exceeds the footprint
cap at 2,577.24 MiB. The adopted binding uses one-row typed conversions and
separate numeric views. Complete generic coverage assembles all 95 rows. The
prototype source and replay pass within the cap. The canonical source group
takes 197.31 s and peaks at 1,276.77 MiB. Final qualification
takes 335.28 s and peaks at 2,276.27 MiB. Both final guards
clean their owned workers. All new modules use default heartbeats.

The explicit inventory has 81,365 roots. It retains all 80,755 prior
roots and every established root. Source and interface freshness, source-layer
checks, static checks and workflow syntax pass. CI checks all four captures.
Original objects remain in functional-base-pilot-original-oleans. Evidence
prefixes are functional-base-canonical and functional-base-pilot-qualification.
The narrow prototype and its exact controls remain in the checker evidence
folder. No cold full-build gain is claimed.

The other 18 base captures remain open. Other numerical argument and frame
families also remain. Item 3 is not complete. The hourly follow-up stays active.
Full frontend validation, environment audit and baseline refresh, full
transitive replay, cold full measurements and Linux qualification did not run.
They remain pending for implementation review. The known aggregate ownership
collision stays deferred. No aggregate pass is claimed.

## Complete functional base family

All 22 native functional base captures now use complete kernel checks. The other
18 captures reuse the qualified checker and exact source bindings. Each capture
keeps one closed result. All original port and relation facts select that result.
The original recipe relation and gate.inputResidual stay exact. All source terms,
zero coefficients and term order stay bound. No caller premise changes. The
semantic finalizer and complete step captures stay unchanged. Both cache modes
stay required. The remaining 20 old base shards are gone. No functional
base proof shard remains.

All 7,776 original public declarations in the remaining captures stay
available. A kernel control accepts all 2,859 old theorem types.
All 4,917 old data Expr values are identical. All 144 selected modules
pass source checks and replay. They include all 18 finalizers and 36 direct
consumers. Replay uses the standard 32 MiB stack. It skips no safe dependency.
All 9,795 focused axiom checks use only the three allowed axioms.
Thirty-six exact capture controls pass. The kernel rejects all thirty-six
mutations. The shared controls and opaque-data rejection retain their qualified
pilot results. All three expanded base generator controls and five step
generator controls pass.

The six larger source captures take 157.72 s and peak at
1,027.34 MiB. Their qualification takes 258.44 s
and peaks at 2,277.91 MiB. The other twelve source captures take
242.20 s and peak at 928.54 MiB. Their qualification
takes 350.34 s and peaks at 2,274.95 MiB. All guards
clean their owned workers. All new modules use default heartbeats. The four
pilot capture outputs stay unchanged. No cold full-build gain is claimed.

The explicit inventory has 82,178 roots. It retains all 81,365 prior roots
and every established root. Source and interface freshness, source-layer checks,
static checks and workflow syntax pass. CI checks the complete family. Original
objects remain in functional-base-remaining-original-oleans. Evidence prefixes
are functional-base-remaining-dense and functional-base-remaining-ordinary.

Item 3 remains open. Other numerical argument and frame checks remain. Counter
frames, history erasure and generic argument checks need migration. Parametric
semantic proofs need a scope check. Decoder interpretation and program-dependent
setup stay excluded. The hourly follow-up stays active. Full frontend validation,
environment audit and baseline refresh, full transitive replay, cold full
measurements and Linux qualification did not run. They remain pending for
implementation review. The known aggregate ownership collision stays deferred.
No aggregate import pass is claimed.

## Complete counter-frame pilot

AddSub now uses one complete counter-frame result per cache mode. The proved
NumericCounterFrameChecks.check_sound derives the exact six original checks.
The source binds all exported columns, slots, address round trips, source
polynomials and helper polynomials. It retains every term and zero coefficient.
The strict importer accepts closed natural data only. A separate complete
kernel equality binds the data. The original assignment and semantic finalizers
stay unchanged. No caller premise changes. Both captures use default heartbeats.

All 26 original public declarations remain. A kernel control accepts all
22 old theorem types. All 4 imported data Expr values are identical.
All 23 selected modules pass source checks and replay. They include the direct
query, memory and oracle consumers in both modes. Replay uses the standard
32 MiB stack. It skips no safe dependency. All 82 focused axiom checks use
only the three allowed axioms. Thirteen exact controls pass. The kernel rejects
all thirteen mutations. The strict opaque-data rejection and legacy importer
control pass. All three Python generator controls pass.

The source guard takes 55.67 s and peaks at 859.76 MiB. The first
qualification run passes consumers, preservation and axiom checks. It then stops
on a reserved field name in a mutation control. Explicit field quoting fixes
that control. The corrected complete control group takes 53.57 s and peaks
at 446.93 MiB. The earlier passed checks are reused. All guards clean
their owned workers. Source and interface freshness, static checks, source-layer
checks and workflow syntax pass. CI checks both cache modes. No cold full-build
gain is claimed.

The explicit inventory has 82,210 roots. It retains all 82,178 prior roots
and every established root. Original objects remain in
counter-frame-pilot-original-oleans. Evidence prefixes are counter-frame-pilot
and counter-frame-prototype. The first prototype rejects a numeric type alias;
the strict importer now admits that natural-data alias. Both canonical captures
pass after the correction.

The other 20 counter-frame captures remain open. Dense prototypes are not
adopted. History erasure and numerical argument checks also remain. Item 3 is
not complete. The hourly follow-up stays active. Full frontend validation,
environment audit and baseline refresh, full transitive replay, cold full
measurements and Linux qualification did not run. They remain pending for
implementation review. The known aggregate ownership collision stays deferred.
No aggregate import pass is claimed.

## Complete counter-frame family

All 22 counter-frame captures now use one complete kernel result per capture.
The other 20 captures use the qualified numeric checker and exact source
binding. All six original predicates remain exact. Each source and helper
polynomial keeps every term, coordinate and zero coefficient. The original
assignment and semantic finalizers stay unchanged. No caller premise changes.
Both cache modes stay required. Every counter-frame module uses default
heartbeats. The two pilot outputs stay unchanged.

All 260 original public declarations in the remaining captures stay
available. A kernel control accepts all 220 old theorem types. All
40 imported data Expr values are identical. All 200 selected modules pass
source checks and replay. They include 100 direct query, memory and oracle
consumers. Replay uses the standard 32 MiB stack. It skips no safe dependency.
All 820 focused axiom checks use only the three allowed axioms. Sixty exact
source controls pass. The kernel rejects all sixty mutations. The shared exact
controls, opaque-data rejection and legacy importer retain their pilot results.
All three expanded Python generator controls pass.

The six larger source captures take 166.39 s and peak at
1,955.09 MiB. Their qualification takes 320.64 s and peaks at
2,282.42 MiB. The other fourteen source captures take 294.55 s and
peak at 941.73 MiB. Their qualification takes 561.47 s and peaks at
2,276.60 MiB. All guards clean their owned workers. Source and interface
freshness, static checks, source-layer checks and workflow syntax pass. CI checks
the complete family. No cold full-build gain is claimed.

The explicit inventory has 82,290 roots. It retains all 82,210 prior roots
and every established root. Original objects remain in
counter-frame-remaining-original-oleans. Evidence prefixes are
counter-frame-remaining-dense and counter-frame-remaining-ordinary. The complete
dense prototypes remain in counter-frame-blake-prototype. Canonical source and
replay replace those temporary source paths for adoption.

Item 3 remains open. History erasure and numerical argument checks remain.
Parametric semantic proofs need a scope check. Decoder interpretation and
program-dependent setup stay excluded. The hourly follow-up stays active. Full
frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision
stays deferred. No aggregate import pass is claimed.

## Complete history-erasure pilot

AddSub now uses one complete history-erasure result per cache mode. The proved
NumericHistoryErasureChecks.check_sound derives the exact original predicates.
It retains history uniqueness, arithmetic erasureCheck and exact field
substitution equality. The arithmetic check keeps all three original branches.
It does not replace field equality with an untouched-coordinate condition.
Complete kernel bindings retain every polynomial term, zero coefficient and
coordinate. The original semantic finalizers stay unchanged. No caller premise
changes. Both captures use default heartbeats.

The first materializer reaches the recursion limit at the clock coefficient.
Component controls isolate this coefficient. Coordinates, ordinary source rows
and protected fields pass separately. The kernel proves the exact inverse value
2013262081 from a multiplication check. A generic equality binds the numeric
clock assertions to the original assertions. A second proved equality binds
numeric substitution to the original typed substitution. The ofSource_eq theorem
composes these exact equalities. The complete source binding unfolds only the
two named protected-polynomial aliases. The original source construction stays
in the soundness statement. The larger recursion override is removed.

All 70 original public declarations remain. This includes both original
history modules and their direct helper consumers. A kernel control accepts all
54 old theorem types. All 16 imported data Expr values are identical.
These values include both helper canonical functions. All 21 selected modules
pass source checks and replay. They include the helper, counter, query and
materialized-witness consumers in both modes. Replay uses the standard 32 MiB
stack. It skips no safe dependency. All 176 focused axiom checks use only the
three allowed axioms. Thirteen exact controls pass. The kernel rejects all
thirteen mutations. Opaque-data rejection, the legacy importer and all three
Python generator controls pass.

The updated shared group takes 8.36 s and peaks at 832.90 MiB. The final
nine-module source tail takes 38.49 s and peaks at 885.13 MiB. It reuses the
passed importer and cached Inputs results. The first qualification misses a
helper import in its axiom query. Its passed consumers and preservation checks
are reused. The corrected qualification takes 81.09 s and peaks at
2,263.68 MiB. All guards clean their owned workers. Temporary debug prints
are removed. Source and interface freshness, static checks, source-layer checks
and workflow syntax pass. CI checks both cache modes. No cold full-build gain is
claimed.

The explicit inventory has 82,348 roots. It retains all 82,290 prior roots
and every established root. Original objects remain in
history-erasure-original-oleans. This baseline also holds all direct helper
consumer objects. Evidence prefixes are history-erasure-pilot,
history-generic-clock and history-materializer. The earlier whole typed
materializers remain unadopted.

The other 20 history captures remain open. Dense prototypes are not adopted.
Numerical argument checks and other frame families need a scope check. Item 3
is not complete. The hourly follow-up stays active. Full frontend validation,
environment audit and baseline refresh, full transitive replay, cold full
measurements and Linux qualification did not run. They remain pending for
implementation review. The known aggregate ownership collision stays deferred.
No aggregate import pass is claimed.

## Complete history-erasure family

All 22 history-erasure captures now use one complete kernel result per
capture. The other 20 captures use the qualified numeric checker and exact
source binding. All original erasure predicates remain exact. Every original
and erased polynomial keeps every term, coordinate and zero coefficient. The
original semantic finalizers stay unchanged. The proved clock coefficient and
numeric substitution factories retain equality with the full original source
model. No caller premise changes. Both cache modes stay required. Every
history-erasure module uses default heartbeats. The two pilot outputs stay
unchanged.

All 998 original public declarations in the remaining captures stay available.
A kernel control accepts all 838 old theorem types. All 160 imported data Expr
values are identical. All 180 selected modules pass source checks and replay.
They include 80 direct helper, counter, query and materialized witness
consumers. Preservation covers each history module and its helper consumer.
Every original helper canonical value stays identical. Replay uses the
standard 32 MiB stack. It skips no safe dependency. All 2,058 focused axiom
checks use only the three allowed axioms. Sixty exact source controls pass.
The kernel rejects all sixty mutations. The shared exact controls, opaque-data
rejection and legacy importer retain their pilot results. All three expanded
Python generator controls pass.

The six larger source captures take 211.09 s and peak at 2,486.90 MiB. Their
qualification takes 456.11 s and peaks at 2,266.52 MiB. The other fourteen
source captures take 299.79 s and peak at 1,059.85 MiB. Their qualification
takes 519.70 s and peaks at 2,276.23 MiB. All guards clean their owned
workers. Source and interface freshness, static checks, source-layer checks
and workflow syntax pass. CI checks the complete family. No cold full-build
gain is claimed.

The explicit inventory has 82,448 roots. It retains all 82,348 prior roots and
every established root. Original objects remain in history-erasure-original-
oleans. Evidence prefixes are history-erasure-remaining-dense and history-
erasure-remaining-ordinary. The complete dense prototypes remain in history-
erasure-blake-prototype. Canonical source and replay replace those temporary
source paths for adoption.

Item 3 remains open. Numerical argument checks and other frame facts remain.
Parametric semantic proofs need a scope check. Decoder interpretation and
program-dependent setup stay excluded. The hourly follow-up stays active. Full
frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They
remain pending for implementation review. The known aggregate ownership
collision stays deferred. No aggregate import pass is claimed.

## Complete native Clean argument pilot

WordMemory now checks all native Clean arguments with one result per cache
mode. Each capture covers nine generic fields, three range arguments and eight
timestamp arguments. NumericCleanArgumentChecks.ofNative_check proves exact
Boolean equality with the original CleanExpression.nativeCheck. The adapter
reuses NumericFunctionalBaseChecks.check_sound. It checks every original full
bank round trip and exact polynomial equality. Both polynomial sides retain all
terms, zero coefficients and order. The port flag is true because this predicate
has no base classification test. The proved Boolean equality keeps that choice
explicit. No caller premise changes.

Original expression definitions precede numeric imports. All old generic part
names, vectors and scalar argument lists remain. All check facts select one
complete result. The value, bound and field-match facts retain their original
references and proofs. Two old generic proof shards are gone. All 160 original
public declarations remain. A kernel control accepts all 112 old theorem
types. All 48 imported Expr values are identical. Both modes use default
heartbeats.

All 22 selected modules pass source checks and replay. These include both
CleanClosedNative and PhysicalClosedNative consumers in both modes. Replay uses
the standard 32 MiB stack. It skips no safe dependency. All 246 focused axiom
checks use only the three allowed axioms. Nine exact controls pass. The kernel
rejects all nine mutations. All three legacy importers pass. The existing strict
natural-data importer retains its qualified opaque-payload rejection. All three
Python generator controls pass.

The source guard takes 78.99 s and peaks at 857.76 MiB. Qualification
takes 67.12 s and peaks at 2,261.15 MiB. Both guards clean their owned
workers. Source and interface freshness, static checks, source-layer checks and
workflow syntax pass. CI checks both cache modes. No cold full-build gain is
claimed.

The explicit inventory has 82,530 roots. It retains all 82,448 prior roots
and every established root. Original scalar modules, generic parts and generic
aggregates stay in clean-argument-original-oleans. This baseline has 136 modules
for all 22 cases. Evidence prefixes are clean-argument-pilot. The other 20 cases
remain open. Dense prototypes are not adopted. Parametric closed lookup proofs
and other numerical frame families need a scope check.

Item 3 remains open. The hourly follow-up stays active. Full frontend
validation, environment audit and baseline refresh, full transitive replay,
cold full measurements and Linux qualification did not run. They remain pending
for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Dense native Clean argument captures

Both BlakeRound modes now check all native Clean arguments with one result per
capture. Each result covers 1,241 rows. These rows contain 1,152 generic fields
and 89 timestamp arguments. The checker uses the original source fields,
native fields and full bank. NumericCleanArgumentChecks.ofNative_check proves
exact Boolean equality with the old nativeCheck. The source bindings retain
all coefficients, zero terms and term order.

Each capture uses bounded numeric data commands. Complete bindings cover each
source row. The complete result derives all old check facts. The semantic value,
bound and field match proofs retain their original references. Small typed
windows select the compatibility facts. Each window has an exact source
equality. The proved checked_window lemma derives each window from the same
complete result. These windows contain no separate numerical check.

A whole-check probe builds in 2.94 s and replays in 2.65 s. The first full
projection variant did not finish in 385.94 s. Its guard was stopped safely.
The bounded projection variant builds in 18.74 s and replays in 5.57 s. These
measurements use cached imports. They do not measure a cold full build.
The first prototype batch reached its 900-second limit after all data and
binding checks passed. Separate bounded canonical phases complete that work.

All 8,192 old public declarations remain. Kernel preservation accepts
all 5,320 old theorem types. All 2,872 imported Expr values are
identical. The 48 old generic proof shards are gone. Both WordMemory pilot
outputs remain byte for byte unchanged. Every new module uses default
heartbeats.

All 21 selected modules pass source checks and replay. These include
CleanClosedParts.Shared, CleanClosedNative and CleanWitnessNative consumers in
both modes. The cached wrappers also pass after their canonical data and
bindings. Replay uses the standard 32 MiB stack. It skips no safe dependency.
All 21,868 focused axiom checks use only the three allowed axioms. Eight exact
controls pass. The kernel rejects all eight mutations. These controls cover
both ends of the complete source and both ends of the projection windows.
The window mutation removes the complete selected window. It avoids comparing
different typed field expressions. Both complete preservation and axiom groups pass for each case before the
original slow control is stopped. The final control phase
reuses those records and the completed source and replay records. One earlier
script selected a PhysicalClosed consumer for a worker. The corrected script
checks the actual worker consumer chain.
The shared pilot controls and three legacy importers retain their prior passes.
All three expanded Python controls pass.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| window-checker | 4.07 s | 830.12 MiB |
| BlakeRoundCached-tail | 45.31 s | 1,104.17 MiB |
| BlakeRoundCached-data | 217.56 s | 847.35 MiB |
| BlakeRoundCached-bindings | 559.91 s | 1,609.28 MiB |
| BlakeRoundUncached-data | 216.24 s | 844.84 MiB |
| BlakeRoundUncached-bindings | 557.15 s | 1,607.49 MiB |
| BlakeRoundUncached-tail | 45.17 s | 1,082.98 MiB |
| blake-qualification | 31.55 s | 520.32 MiB |

The prior qualification phase peaks at 2,289.88 MiB. It stops after
327.48 s. The table's qualification row measures the final control phase. The prior
earlier qualification completes both preservation and axiom groups before its
slow typed mutation is stopped. Every guard cleans its owned workers.
Source and interface freshness, static checks, source layer checks, source
import graph checks and workflow syntax pass. CI checks both cache
modes. The explicit inventory has 96,197 roots. It retains all 82,530 prior
roots and every established root. Evidence uses the clean-argument-blake and
clean-argument-BlakeRound prefixes. The original objects remain in
clean-argument-original-oleans.

Item 3 remains open. Eighteen Clean argument captures still need adoption.
Lookup source and worker port numerical shards also remain. Other frame and
argument families need a scope check. Parametric semantic proofs need a separate
scope check. Program-dependent setup and captured decoder interpretation stay
outside this rollout. The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Complete native Clean argument rollout

All 22 captures now use one complete native Clean argument result per capture.
The remaining 18 captures use the proved adapter from WordMemory and
BlakeRound. They use the same pattern for source bindings. The results cover every range argument, timestamp
argument and generic field. They preserve the exact original nativeCheck.
They retain every polynomial coefficient, zero term and term order. Full bank
round trips keep their original references.

All 7,634 original declarations remain in the 18 captures. Kernel
preservation accepts all 5,048 old theorem types. All 2,586 imported
Expr values are identical. These include every scalar expression, generic
part expression, generic vector and complete argument list. The old semantic
value, bound and field match proofs remain. The 44 remaining generic proof
shards are gone. No native Clean argument proof shard remains. The four
qualified WordMemory and BlakeRound captures remain byte for byte unchanged.
Every new capture uses default heartbeats.

All 178 selected modules pass source checks and replay. The selected consumers
follow the actual source graph. Worker cases use their available Shared,
CleanClosedNative and CleanWitnessNative modules. Executor cases also check
PhysicalClosedNative. Replay uses the standard 32 MiB stack. It skips no safe
dependency. All 19,804 focused axiom checks use only the three allowed axioms.
The dense group passes 24 exact controls and 24 kernel mutation rejections.
The ordinary group passes 40 exact controls and 40 kernel mutation rejections.
The controls cover both source ends and both projection-window ends. The shared
controls and legacy importers retain their prior passes. All three expanded
Python controls pass for the complete 22-case family.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| dense | 440.23 s | 916.71 MiB |
| dense-qualification | 222.27 s | 2,295.42 MiB |
| ordinary | 375.72 s | 871.52 MiB |
| ordinary-qualification | 391.86 s | 2,281.02 MiB |

All guards clean their owned workers. Source and interface freshness, static
checks, source layer checks, source import graph checks and workflow syntax
pass. CI keeps both cache modes required. The explicit inventory has
108,277 roots. It retains all 96,197 prior roots and every established root.
Original objects remain in clean-argument-original-oleans. Evidence uses the
clean-argument-remaining prefixes. No gain in a cold full build is claimed.

Item 3 remains open. Numerical LookupSource and WorkerPorts shards remain.
Other frame and argument checks need a scope audit. Parametric semantic
proofs need a separate scope audit. Header heartbeat budgets also need a scope
audit. Program-dependent setup and captured decoder interpretation stay outside
this rollout. The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Complete lookup source pilot

Both AddSub modes now use one complete lookup source result per capture.
NumericLookupSourceChecks.ofAgreement_check proves exact Boolean equality with
the original bank check and source agreement check. It keeps the complete
original relation bank and witness. It does not require an empty witness.
The role and coverage adapter proves exact Boolean equality with each original
flag. NumericFunctionalBaseChecks.check_sound derives all old check facts.

The data phase reconstructs every actual operand. It retains every registry
and expansion binding. It imports the original source fields and actual native
recipes. It preserves all polynomial coefficients, zero terms and term order.
The result includes all source agreement and bank checks, base roles, mask
roles, setup flags and exact source coverage. The original sourceField,
sourceQuery, match and reduction finalizers remain. Exact lookup and RAM
premises keep their original references. The field transport checks also cover
the decoder fields. They do not interpret decoded instructions.

All 414 original declarations remain. Kernel preservation accepts all
248 old theorem types. All 166 imported Expr values are identical.
Both captures use default heartbeats. All 18 selected modules pass source
checks and replay. These include both TableNative and FunctionalLinksNative
consumers. Replay uses the standard 32 MiB stack. It skips no safe dependency.
All 912 focused axiom checks use only the three allowed axioms.

Nine exact controls pass. The kernel rejects all nine mutations. They cover a
nonempty witness, a changed witness coefficient, a missing bank round trip,
a false role, a dropped zero term and both ends of each complete source.
The nonempty witness fixture uses the source format's Montgomery encoding of
one. The original legacy importer passes. Three phase controls reject missing
checker facts, checker facts in the input phase and unsupported phases.
All three Python generator controls pass. The public premise fixture now
includes the numeric payloads and checker sources that inventory generation
reads. Its fourteen-profile control passes. It rejects tuple and decoder-field
order mutations. CI checks both modes.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| numeric-lookup-source-checker | 3.44 s | 787.64 MiB |
| lookup-source-importer | 8.25 s | 782.20 MiB |
| lookup-source-pilot-source | 49.71 s | 838.29 MiB |
| lookup-source-controls | 27.71 s | 331.45 MiB |
| lookup-source-pilot-qualification | 35.85 s | 2,267.77 MiB |
| lookup-source-importer-controls | 6.72 s | 442.27 MiB |

All guards clean their owned workers. Source and interface freshness, static
checks, source layer checks, the source import graph and workflow syntax pass.
The explicit inventory has 108,770 roots. It retains all 108,277 prior roots
and every established root. The 42 original lookup source module objects stay
in lookup-source-original-oleans. Evidence uses the lookup-source and
numeric-lookup-source prefixes. No gain in a cold full build is claimed.

The other 20 lookup source captures remain open. The next scaling gate covers
both BlakeRound modes. Numerical worker port checks, other frame and argument
checks and the header budget audit also remain. Program-dependent setup and
captured decoder interpretation stay outside this rollout. Item 3 remains open.
The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Complete dense lookup source checks

Both BlakeRound modes now use one complete lookup source result per capture.
Each result covers all 1,437 rows, including all 1,152 field agreements.
The proved adapter keeps the exact original relation bank and witness.
Complete source bindings retain every coefficient, zero term and term order.
The original semantic finalizers and exact lookup and RAM premises remain.
The rollout retires 20 old foundation and proof shard modules.

All 15,526 original declarations remain. Kernel preservation accepts
all 9,388 old theorem types. All 6,138 imported Expr values
are identical. All 16 selected modules pass canonical source builds and
replay. These include both TableNative and FunctionalLinksNative consumers.
Replay uses the standard 32 MiB stack. It skips no safe dependency.
All 35,962 focused axiom checks use only the three allowed axioms.
Four new exact source controls pass. The kernel rejects all four mutations.
The prior generic witness, role, bank and legacy controls retain their passes.
All three expanded Python generator controls pass. Only the first data import
command in each dense Inputs module has a scoped two-million heartbeat budget.
It reconstructs the complete original affine definitions. Its bounded operand
data commands retain one whole checker result. Both whole and bounded first
commands exceeded the default budget in canonical source checks. All other new
modules use default heartbeats. CI keeps both cache modes required.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| lookup-source-large-BlakeRoundCached-canonical | 554.56 s | 1,455.10 MiB |
| lookup-source-large-BlakeRoundCached-qualification | 47.93 s | 2,267.54 MiB |
| lookup-source-large-BlakeRoundUncached-canonical | 540.27 s | 1,455.70 MiB |
| lookup-source-large-BlakeRoundUncached-qualification | 47.26 s | 2,275.56 MiB |

All guards clean their owned workers. Source and interface freshness, static
checks, source layers, the source import graph and workflow syntax pass.
The explicit inventory has 130,022 roots. It retains all 108,770 prior
roots and every established root. Original objects remain in
lookup-source-original-oleans. Evidence uses the lookup-source-large prefixes.
No gain in a cold full build is claimed.

The other 18 lookup source captures remain open. Numerical worker port checks,
other frame and argument checks and the header budget audit also remain.
Program-dependent setup and captured decoder interpretation stay outside this
rollout. Item 3 remains open. The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Complete dense source freshness checks

Both dense table captures now use one complete numeric freshness result.
Each result covers all 632 original source coordinates and both multiplicity
addresses. Exact bindings keep the complete original source and target vectors.
The proved address encoding keeps every GKR address class. check_sound derives
the exact original addressEqual predicates. The original table data, layouts,
roles and semantic finalizers remain.

The old cached TableNative source builds. Its replay exceeds the physical
footprint cap. A control rebuild with the archived original lookup objects
reproduces that replay failure. The control peaks at 2,562.12 MiB. The new
cached TableNative source builds in 2.23 s and replays in 1.78 s. Its guard
peaks at 836.73 MiB. The limits stay unchanged. Both cache modes pass.

All 34 original table declarations remain. Kernel preservation
accepts all 24 old theorem types. All 10 imported Expr
values are identical. All 13 selected modules pass source and standard
32 MiB replay. They skip no safe dependency. Together, the coupled lookup and
freshness step checks 27 distinct modules. All 870 focused
freshness and table axiom checks use only the three allowed axioms.
Ten exact controls pass. The kernel rejects all ten mutations. They cover
collisions, address classes, zero coordinates, complete targets and both ends
of each native source vector. The importer rejects facts of the wrong type.
The original AddSub table importer also passes source and replay. All three
Python generator controls pass. All new freshness modules use default heartbeats.
Both dense table wrappers also use default heartbeats. CI keeps both modes.

The other 20 table freshness captures remain open. They retain the legacy
importer path. The other 18 lookup source captures also remain open. Other
numerical frame and argument families and the header budget audit remain.
Item 3 stays open. The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Complete source multiplicity freshness family

All 22 native table captures now use one numeric freshness result per capture.
The final 20 captures keep every original source coordinate and multiplicity
address. Complete kernel bindings cover both full vectors. check_sound derives
the exact original addressEqual facts. The source tables, layouts, roles and
semantic finalizers keep their original references.

All 436 old declarations in the final 20 captures remain.
Kernel preservation accepts all 320 old theorem types.
All 116 imported Expr values are identical.
All 100 selected source modules and standard 32 MiB replays pass.
They skip no safe dependency. All 2212 focused axiom queries use only
the three allowed axioms. The kernel rejects all 60 captured binding mutations.
All 60 exact controls pass. Four shared exact and kernel mutation pairs pass.
The importer rejects facts of the wrong type. The default legacy importer also
passes. All three expanded Python generator controls pass. Both adopted dense
pilot outputs stay unchanged.

All new freshness modules use default heartbeats. All 22 TableNative wrappers
now also use default heartbeats. Their 22 old four-million overrides are gone.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| source-freshness-remaining-dense-source | 132.28 s | 857.04 MiB |
| source-freshness-remaining-dense-qualification | 92.54 s | 2,280.74 MiB |
| source-freshness-remaining-ordinary-source | 271.63 s | 838.68 MiB |
| source-freshness-remaining-ordinary-qualification | 217.41 s | 2,275.88 MiB |
| shared controls | 16.00 s | 419.16 MiB |

All guards clean their owned workers. Source and interface freshness, static
checks, source layers, the source import graph and workflow syntax pass.
CI keeps both cache modes required. The inventory has 131,598 roots.
It retains all 130,022 prior roots and every established root. Original table
objects remain in source-freshness-original-oleans. Evidence uses the
source-freshness-remaining prefixes. No cold full-build gain is claimed.

The remaining 18 lookup source captures stay open. Numerical worker port
checks, other frame and argument families and the header budget audit also
remain. Program-dependent setup and captured decoder interpretation stay
outside this rollout. Item 3 remains open. The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Complete native lookup source family

All 22 captures now use one complete numeric lookup source result per capture.
The final 18 captures retain every original witness and relation bank.
Complete source bindings keep every polynomial coefficient, zero term and term
order. The result covers every role, bank round trip, field agreement, mask,
setup flag and exact source coverage. The original semantic finalizers and
exact lookup, request and RAM premises remain.

All 16,004 old declarations in the final 18 captures remain.
Kernel preservation accepts all 9,658 old theorem types.
All 6,346 imported Expr values are identical.
All 144 selected source modules and standard 32 MiB replays pass.
They include every TableNative and FunctionalLinksNative direct consumer.
They skip no safe dependency. All 36,604 focused axiom queries use only
the three allowed axioms. All 36 new exact controls pass. The kernel rejects
all 36 mutations. Prior generic witness, bank, role and legacy controls retain
their passes. All three expanded Python generator controls pass.

All 18 new captures use default heartbeats. Only the two previously qualified
dense source-definition imports keep their scoped two-million budgets.
The four adopted AddSub and BlakeRound outputs stay unchanged. All lookup
source semantic proof shards are gone. Bounded data commands and complete
source-binding leaves retain one whole semantic result per capture.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| lookup-source-remaining-dense-source | 339.09 s | 897.43 MiB |
| lookup-source-remaining-dense-qualification | 161.49 s | 2,281.52 MiB |
| lookup-source-remaining-ordinary-source | 323.91 s | 846.62 MiB |
| lookup-source-remaining-ordinary-qualification | 275.30 s | 2,278.09 MiB |

All guards clean their owned workers. Source and interface freshness, static
checks, source layers, the source import graph and workflow syntax pass.
CI keeps both cache modes required. The inventory has 152,108 roots.
It retains all 131,598 prior roots and every established root. Original objects
remain in lookup-source-original-oleans. Evidence uses the lookup-source-remaining
prefixes. No cold full-build gain is claimed.

Numerical worker port checks, other frame and argument families and the header
budget audit remain. Program-dependent setup and captured decoder interpretation
stay outside this rollout. Item 3 remains open. The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Complete native worker port family

All eight worker captures now use one complete numeric result per capture.
Both cache modes stay required. This family replaces 32 old modules with 50
modules, including two shared checker and importer modules. Separate data and
binding modules keep each build within the memory cap. Exact source bindings
cover every original column address, previous-clock address and history-index bound. Address codes
preserve each address class. The checker proves the three original predicates.
The original read/write token proofs and their exact premises remain.

All 268 original declarations remain. Kernel preservation accepts
all 228 old theorem types. All 40 imported Expr values
are identical. This includes each old block and the history predicate.
The 24 old shard and shared files are retired. Their public facts remain as
corollaries of the whole result. No worker port semantic proof shard remains.

All 50 selected source modules and standard 32 MiB replays pass.
They skip no safe dependency. All 2,998 focused axiom queries use only
the three allowed axioms. All 38 exact controls pass. The kernel rejects
all 38 mutations. The strict importer rejects an opaque payload.
All three Python generator controls pass. Complete kernel length bindings
check the dimensions read from the original source. Source hashes guard the
dimension plan. Source and interface freshness pass. CI checks both modes.

All new worker captures and all eight native wrappers use default heartbeats.
Bounded data commands use 16 address pairs or 32 bounds. Source bindings use
four address pairs or 16 bounds. The largest capture has 507 pairs and 86 bounds.
Local transparency settings keep the elaborator from unfolding complete data
recipes during proof assembly. The kernel still checks every exact conversion.
The largest binding builds in 35.29 s and replays in 32.14 s. Its complete
certificate builds in 1.93 s and replays in 1.82 s. These are focused prototype
measurements. The canonical pair also passes. No cold full-build gain is claimed.

The initial assembly exceeded the default heartbeat budget. The local
transparency settings resolve that cost. The first control runner had a syntax
error. The corrected runner passes and reuses all passed preservation checks.
The initial dimension reader used an incomplete search path. The corrected
reader and the canonical dimension exporter pass.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| Dense source continuation | 225.99 s | 1,145.87 MiB |
| Other six sources | 210.17 s | 953.38 MiB |
| Final controls and dimension freshness | 163.53 s | 665.82 MiB |

The cached Inputs module passed in the initial source phase. The continuation
reuses that pass. All guards clean their owned workers. The inventory has
154,572 roots. It retains all 152,108 prior roots and every established
root. Original objects remain in worker-ports-original-oleans. Evidence uses
the worker-ports prefixes.

Helper-validity transport facts and the header-budget audit remain open.
Other frame and argument families still need a scope audit. Some already use
whole checks. Parametric token and lookup proofs stay semantic proofs.
Program-dependent setup and captured decoder interpretation stay excluded.
Item 3 remains open. The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full
transitive replay, cold full measurements and Linux qualification did not run.
They remain pending for implementation review. The known aggregate ownership
collision stays deferred. No aggregate import pass is claimed.

## Complete helper-validity pilot

The AddSub and BlakeRound captures now use one complete helper-validity result
in each cache mode. The other 18 captures remain open. The checker proves the
original protected-field, recursive borrow and transport predicates.
Transport keeps exact polynomial list equality. It preserves term order and
zero terms. It does not replace that reference with normalized equality.
Protected fields retain the original erasure-substitution equality.
Every original bank round trip and strict borrow bound remains.

All 258 old declarations remain. Kernel preservation accepts all
242 old theorem types. All 16 imported Expr values are identical.
The data phase declares execute, profile, normalized and canonical before the
numeric imports. The original semantic finalizers remain. Each old per-index
transport fact now selects the complete result. The importer keeps its legacy
path. It rejects semantic check injection in the data phase and wrong fact types.

All 75 selected source modules and standard 32 MiB replays pass.
They include 48 direct consumers. They skip no safe dependency.
All 1,320 focused axiom queries use only the three allowed axioms.
All 62 exact controls pass. The kernel rejects all 62 mutations. These controls
include reordered terms and a dropped zero term. The strict importer rejects an
opaque payload. All three Python generator controls pass. Dimension freshness,
source and interface freshness, source layers, the source graph and workflow
syntax pass. CI keeps both modes required.

All four pilot wrappers and new capture modules use default heartbeats.
Four-row data commands and complete source bindings cover all three field lists.
The largest capture has 90 protected fields and 89 borrow and transport rows.
Its bindings build and replay in about 23 s. Its whole certificate takes about
2 s for each step. Separate data and binding modules keep memory bounded.
The four captures use 24 capture modules plus the shared checker and importer.
No cold full-build gain is claimed.

Whole dense data materialization hit the default heartbeat limit. Bounded data
commands pass. A combined data-view and typed-source control exceeded memory.
The adopted controls check each exact view and source piece separately.
Both stages already pass in the complete source-binding proof.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| Canonical pilot source and replay | 251.95 s | 1,215.79 MiB |
| Final exact and mutation controls | 238.74 s | 641.82 MiB |
| Direct consumers | 252.02 s | 959.45 MiB |
| Dimension freshness | 41.63 s | 434.76 MiB |

All guards clean their owned workers. The inventory has 155,424 roots.
It retains all 154,572 prior roots and every established root. Original native
and direct-consumer objects remain in the helper-validity evidence folders.
The remaining 18 helper captures and the header-budget audit remain open.
Other frame and argument families still need a scope audit. Some already use
whole checks. Parametric semantic proofs stay outside the numeric rollout.
Item 3 remains open. The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Complete native helper-validity family

All 22 captures now use one complete helper-validity result per capture.
The final 18 keep all original protected-field erasure checks, recursive borrow
checks and exact transport equations. They preserve every polynomial term,
zero term and term order. Full bank round trips and strict borrow bounds remain.
The original profile, normalization, canonical assignment and semantic finalizers
remain. All old per-index transport names select the whole result.

The final 18 retain all 568 original declarations.
Kernel preservation accepts all 496 old theorem types.
All 72 imported Expr values are identical.
All 327 selected source modules and standard 32 MiB replays pass.
They include all 216 selected direct consumers. They skip no safe dependency.
All 3,082 focused axiom queries use only the three allowed axioms.
All 252 exact controls pass. The kernel rejects all
252 mutations. The pilot's shared legacy, opaque, phase and
wrong-fact controls retain their passes. All four expanded Python controls pass.

All 22 wrappers and every new capture module use default heartbeats.
The four pilot outputs stay unchanged. Complete numeric views and exact source
pieces bind every captured entry. Each family keeps one whole Boolean result.
The dimension plan includes actual source lengths and source hashes.
CI checks shared controls and both cache modes in separate bounded commands.
The existing memory limits remain. No cold full-build gain is claimed.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| helper-validity-remaining-dense-source | 187.07 s | 1,010.52 MiB |
| helper-validity-remaining-dense-qualification | 354.97 s | 2,307.65 MiB |
| helper-validity-remaining-dense-direct | 355.15 s | 895.12 MiB |
| helper-validity-remaining-ordinary-source | 292.92 s | 866.35 MiB |
| helper-validity-remaining-ordinary-qualification | 697.67 s | 2,281.93 MiB |
| helper-validity-remaining-ordinary-direct | 659.04 s | 877.81 MiB |

All guards clean their owned workers. The inventory has 156,678 roots.
It retains all 155,424 prior roots and every established root.
Original native and direct-consumer objects remain in the helper-validity
baselines. Evidence uses the helper-validity-remaining prefixes.

The scope audit found additional numerical families. HelperImport still checks
each payload agreement, recipe round trip and role set. MemoryImport still
checks each payload expansion, input role, bank input and row fingerprint
certificate. TypingImport still checks each consumer node before it assembles
the whole typing result. These families remain open. Their semantic finalizers,
relation banks and complete witnesses must stay exact. Other metadata and
header budgets still need an audit. Parametric semantic proofs stay outside the
numeric rollout. Item 3 remains open. The hourly follow-up stays active.

Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run. They remain
pending for implementation review. The known aggregate ownership collision stays
deferred. No aggregate import pass is claimed.

## Native payload scaling checkpoint

The next payload family remains unadopted. The generic helper and memory
adapters pass source and kernel replay checks. Each adapter preserves the exact
old bank, role and agreement checks. It keeps the complete relation bank and
witness. The memory adapter keeps the original unsupported-expression branch
and all seven symbolic variables. A generic projection theorem derives one old
operand fact from the whole result and an exact bounded source binding.

Both BlakeRound helper prototypes cover all 89 original helper operands.
All eight prototype source modules and standard 32 MiB replays pass.
Complete bindings retain every encoded port and polynomial term.
The cached data builds in 21.26 s. Its bindings build in 19.78 s.
The uncached data builds in 21.45 s. Its binding replay takes 18.33 s.
Each whole certificate builds and replays in about 2 s.
The paired tail guard peaks at 924.04 MiB and takes 112.85 s.
Three exact controls pass. The kernel rejects changes to a nonempty witness,
its coefficient and a retained zero term. Their guard takes 9.13 s and peaks
at 320.13 MiB. No worker remains.

All prototypes stay in the evidence folder. They are not canonical source.
The native wrappers, metadata facts, complete old-interface preservation,
axiom checks, captured mutations and direct consumers still need qualification.
No payload capture is complete. No cold full-build gain is claimed.
HelperImport and MemoryImport still need their per-payload rollout.
Consumer typing and the remaining metadata/header scope also stay open.
The hourly follow-up stays active. Final lengthy validation stays pending.

## Native helper payload pilot

AddSubCached and AddSubUncached now use one complete helper payload result each.
The checker preserves the exact bank round trips, base roles and helper agreement.
It retains the original relation bank, source, lowered expression and witness.
Complete source bindings retain every coefficient, zero term and term order.
One-entry source bindings derive all old per-operand facts from the whole result.
The original source-query and timestamp reduction proofs remain.
The whole layout, borrow, source-scope and coverage facts remain explicit.
This step does not migrate those metadata checks.

The importer freezes every original data definition before numeric imports.
Its final phase accepts only facts with the original types.
The default phase retains the original importer path.
Both adopted wrappers and every new pilot module use default heartbeats.
All 184 old declarations remain.
Kernel preservation accepts all 122 old theorem types.
All 62 imported Expr values are identical.
All 20 selected source modules and standard 32 MiB replays pass.
They include six direct consumer modules. They skip no safe dependency.
All 308 focused axiom queries use only the three allowed axioms.
All 11 exact controls pass. The kernel rejects all 11 mutations.
These include a nonempty witness, its coefficient, a retained zero term,
and complete captured source windows. Legacy, invalid-phase, wrong-fact and
opaque-payload controls pass. All three Python generator controls pass.
CI requires both cache modes. Source and interface freshness pass.
The qualification guard takes 59.41 s and peaks at 2,271.60 MiB.
The direct-consumer guard takes 26.33 s and peaks at 838.81 MiB.
Both guards clean their owned workers.
The inventory has 156,793 roots. It retains all 156,678 prior roots.
Original helper and memory objects remain in native-payload-original-oleans.
Evidence uses the helper-payload prefixes. No cold full-build gain is claimed.

The BlakeRound pair remains unadopted. Its original data reconstruction exceeds
the default heartbeat budget. A scoped two-million budget builds the cached data
in 33.15 s. Standard-stack replay then reaches the footprint cap at 2,561.52 MiB.
That guard stops safely after 41.37 s and leaves no owned worker.
The next step must isolate and replace the expensive original metadata check.
The prior complete 89-operand payload prototypes remain available in both modes.
No dense payload capture is claimed as qualified.

The other 20 helper payload captures, memory payloads, consumer typing and the
remaining metadata/header scope stay open. The hourly follow-up stays active.
Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run.
They stay pending for implementation review. The known aggregate ownership
collision stays deferred. No aggregate import pass is claimed.

## Structural helper source projection

The importer now derives the exact originalProjection equation from a generic
list-prefix theorem. It binds the complete original source prefix by kernel
conversion. It keeps the original bank, memory placement, address classes and
source order. It adds no caller premise and changes no imported data value.

Fresh replay isolated the old originalProjection proof. It reaches the footprint
cap at 2,570.92 MiB. A separate fresh check isolates historyProjection at
2,564.08 MiB. The new structural proof closes the first obligation.
Both dense cache modes build their complete data sources. Fresh replay accepts
each repaired originalProjection and its complete local dependency closure.
That paired guard takes 46.12 s and peaks at 2,225.82 MiB.
These are target checks. They do not qualify either whole dense module.
The historyProjection obligation remains open.

The generic theorem, importer and both adopted Inputs and native wrappers pass
source checks and standard 32 MiB replay. All 184 original pilot declarations
remain. All 122 old theorem types and 62 exact imported values pass preservation
again. All 310 focused axiom queries use only the allowed three axioms.
The 11 payload control pairs pass again. Three new exact prefix controls pass.
The kernel rejects changes to an address class, coordinate and complete prefix.
Legacy, phase, wrong-fact and opaque controls pass again.
The qualification guard takes 67.98 s and peaks at 2,290.43 MiB.
All guards clean their owned workers. Generator and interface freshness pass.
CI includes the projection controls. The inventory has 156,794 roots and retains
all 156,793 prior roots. The dense data-range experiment stays unadopted in the
evidence folder. Its foundation also hits the cap. Do not repeat that variant.

The dense payload rollout and the remaining implementation stay open.
Full frontend validation, environment audit, full transitive replay, cold full
measurements and Linux qualification stay pending for implementation review.
No whole dense or aggregate import pass is claimed.

## Dense native helper payload captures

BlakeRoundCached and BlakeRoundUncached now use complete helper payload checks.
Each result covers all 89 original candidates. Complete source bindings keep
all original bank round trips, base roles, relation banks and agreement witnesses.
They preserve every coefficient, zero term and term order.
Every old checked, inBank and roles fact selects the same whole result.
The original source-query and timestamp reduction proofs remain.

The importer also derives the exact historyProjection equation from the existing
complete memory input-bank certificate. A generic pair-projection theorem keeps
every history pair, both limb positions and every address class.
This closed proof adds no caller premise. It changes no data definition.
Both complete dense data modules now pass standard 32 MiB replay.
The former projection replay caps are resolved for this metadata module.
The other whole layout, borrow, scope and coverage facts stay explicit.
This step does not claim their separate numeric migration.

All four adopted captures retain 1,826 original declarations.
Kernel preservation accepts all 1,216 old theorem types.
All 610 imported Expr values are identical.
The dense pair alone retains 1,642 declarations, 1,094 theorem types and 548 values.
All 40 selected source modules and standard 32 MiB replays pass.
These include 12 direct consumers. They skip no safe dependency.
All 3,100 focused axiom queries use only the three allowed axioms.
All 19 payload exact controls pass. The kernel rejects all 19 mutations.
Three additional history controls pass and reject changed address classes,
limb order and complete pair coverage. The first history control fixture omitted its bank constructor import.
The corrected explicit bank fixture passes. Legacy, phase, wrong-fact and opaque
controls pass. All three Python generator controls pass.

The dense Inputs commands still exceed the default heartbeat budget after the
structural repairs. The measured cached control stops safely after 18.13 s,
with a 1,253.52 MiB peak. Only these two complete data reconstruction commands
use a scoped two-million budget. All new checkers, bindings, certificates and
four native wrappers use default heartbeats. No header-wide override remains
in the four adopted wrappers. Both cache modes stay required.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| helper-history-integrated | 82.30 s | 1,679.22 MiB |
| helper-payload-dense-canonical2 | 202.10 s | 1,679.32 MiB |
| helper-payload-dense-qualification2 | 8.90 s | 315.55 MiB |
| helper-payload-dense-consumers | 53.69 s | 886.52 MiB |

All guards clean their owned workers. The two initial pilot source outputs stay
unchanged. CI requires all four captures and includes history projection controls.
Source and interface freshness pass. The inventory has 157,916 roots.
It retains all 156,794 prior roots and every established root.
The original helper and memory objects remain in the payload baseline.
Evidence uses helper-history and helper-payload-dense prefixes.
No cold full-build gain is claimed.

The other 18 helper payload captures stay open. Memory payloads, consumer typing
and the remaining metadata/header scope also stay open.
The hourly follow-up stays active. Full frontend validation, environment audit,
full transitive replay, cold full measurements and Linux qualification did not
run. They stay pending for implementation review.
No aggregate import pass is claimed.

## Complete native helper payload family

All 22 helper payload captures now use one complete result per capture.
The final 18 preserve every original agreement, bank round trip and base role.
Complete bindings retain every relation bank, witness, polynomial coefficient,
zero term and term order. The original semantic finalizers remain.
All old checked, inBank, roles, sourceQuery and data names remain.
The four earlier captures stay unchanged.

The final 18 retain all 2,880 original declarations.
Kernel preservation accepts all 1,914 old theorem types.
All 966 imported Expr values are identical.
All 166 selected source modules and standard 32 MiB replays pass.
They include 54 direct consumers. They skip no safe dependency.
All 4,904 focused axiom queries use only the three allowed axioms.
All 72 captured exact controls pass. The kernel rejects all 72 mutations.
The qualified shared legacy, phase, wrong-fact, opaque, witness and projection
controls retain their passes. All three expanded Python controls pass.
Source, interface, static, layer, graph and workflow checks pass.
CI checks every adopted capture, including both cache modes.

Every module in the final 18 uses default heartbeats.
All 22 native helper wrappers now use default heartbeats.
Only the two measured BlakeRound data commands retain scoped two-million budgets.
The existing memory and time limits remain. No cold full-build gain is claimed.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| helper-payload-remaining-dense-source | 187.72 s | 920.64 MiB |
| helper-payload-remaining-dense-qualification | 113.31 s | 2,298.60 MiB |
| helper-payload-remaining-dense-direct | 97.78 s | 858.40 MiB |
| helper-payload-remaining-ordinary-source | 278.76 s | 841.29 MiB |
| helper-payload-remaining-ordinary-qualification | 221.81 s | 2,279.99 MiB |
| helper-payload-remaining-ordinary-direct | 167.58 s | 842.29 MiB |

All guards clean their owned workers. The inventory has 159,724 roots.
It retains all 157,916 prior roots and every established root.
The original 44 helper and memory module objects remain in the payload baseline.
Evidence uses helper-payload-remaining prefixes.

Memory payloads and consumer typing remain open.
The generic memory fingerprint adapter is proved. It has no adopted capture yet.
Memory expansion flags, primitive ports, fingerprint occurrences and mask fields
must retain their original checks and complete witnesses.
The remaining metadata and header scope also needs its audit.
The hourly follow-up stays active. Full frontend validation, environment audit,
full transitive replay, cold full measurements and Linux qualification did not
run. They stay pending for implementation review.
No aggregate import pass is claimed.

## Native memory payload pilot and dense captures

AddSubCached, AddSubUncached, BlakeRoundCached and BlakeRoundUncached now use one
complete memory payload result each. Each result covers the full projection
input list, every primitive expansion flag, every input-bank and base-role check,
every fingerprint occurrence and both mask fields. The fingerprint adapter
retains the original memoryExpression none/some branch, all seven extra variables,
all lifted relations and the complete original witness. Exact bindings retain
all coefficients, zero terms and term order. All old declarations remain.
The original product, source-query, mask and RAM proofs keep their premises.
Whole source-scope, tree and coverage metadata checks stay explicit.
This step does not claim their separate numeric migration.

The four captures retain all 2,080 original public declarations.
Kernel preservation accepts all 1,412 old theorem types.
All 668 imported Expr values are identical.
All 46 selected source modules and standard 32 MiB replays pass.
They include 12 direct consumers. They skip no safe dependency.
Local standard-instance priorities preserve every affected helper Expr value.
The complete old helper theorem types also pass kernel preservation.
Both affected worker captures retain their original values and theorem types.
The first consumer preservation control detected changed field-instance paths.
The local priorities restore the original paths. The focused retry rebuilds only
the four changed helper modules. It reuses eight unchanged consumer passes.
All 6,240 focused axiom queries use only the three allowed axioms.
All 50 exact controls pass. The kernel rejects all 50 mutations.
These include nonempty mask witnesses, changed coefficients, expansion flags,
primitive ports, fingerprint and mask source windows, and projection coverage.
Legacy, phase, wrong-fact and opaque-payload controls pass.
All three Python generator controls pass. Source and interface freshness pass.
Source layers, import graph, changed-source trust checks and workflow syntax pass.
CI requires all four captures and both cache modes.

The old whole projection-port binding exceeded the replay footprint limit.
The adopted binding uses bounded source slices before numeric mapping.
Its generic coverage proof binds every source port to one whole result.
The repaired dense binding passes source and replay in 22.07 s at 883.30 MiB.
The two complete BlakeRound data reconstruction commands exceed the default
heartbeat budget. Only those commands use a scoped two-million budget.
All new checkers, bindings, certificates and four native wrappers use default
heartbeats. No cold full-build gain is claimed.

| Guarded phase | Time | Peak physical footprint |
| --- | ---: | ---: |
| memory-payload-pilot-canonical | 115.35 s | 847.10 MiB |
| memory-payload-dense-canonical3 | 291.76 s | 1,002.40 MiB |
| memory-payload-qualification | 31.75 s | 2,304.04 MiB |
| memory-payload-controls2 | 173.09 s | 405.20 MiB |
| memory-payload-direct3 | 71.06 s | 1,726.21 MiB |
| memory-payload-worker-preservation | 11.96 s | 836.23 MiB |

All guards clean their owned workers. The inventory has 163,824 roots.
It retains all 159,724 prior roots and every established root.
The original helper and memory objects remain in the payload baseline.
Evidence uses memory-payload and memory-projection prefixes.

The other 18 memory payload captures remain open. Consumer typing and the final
metadata/header scope audit also remain open. The hourly follow-up stays active.
Full frontend validation, environment audit and baseline refresh, full transitive
replay, cold full measurements and Linux qualification did not run.
They stay pending for implementation review. No aggregate import pass is claimed.
