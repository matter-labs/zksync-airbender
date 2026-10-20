# Circuit formal verification plan

Finalization of the pending integration work is active, with an hourly follow-up.
The user resumed implementation after manual review on 13 October 2026. Current
coverage, checked counterexamples and machine-check results live in
[Verification status](VERIFICATION_STATUS.md).
[Directory review guide](../lean/human/Human/README.md) separates per-circuit and whole-trace reading.
[Trust and review boundaries](TRUST_AND_REVIEW.md) records provenance and unchecked
connections. Keep these documents as snapshots, without completed-work history.

## Integrated review contract

Start with the composed execution claim in
[Trace/Soundness.lean](../lean/slop/Slop/Final/Trace/Soundness.lean) and its
[public inputs](../lean/human/Human/Helpers/Context/PooledBoundary.lean). The proof path is:

```text
public initialization → preserved write bounds → latest-write reads
                      → circuit operand bounds → original Sail execution
```

The shared `Realizes` property states execution and terminal PC/cell realization
once. Keep public conditions visible: field compatibility, platform/configuration,
initial state/program/domain, modeled tables, logical matching and unresolved
terminal conditions. Derive local bounds, reads, decoder selectors and row
interfaces inside `Slop/`; never assume desired reads, results or decoder answers.

Use Clean's original constraint semantics and original Sail standard-instruction
clauses. Project custom operations use the pinned project specification. Keep the
unchanged-Sail discarded-load restriction distinct from the named Airbender
PC-only-NOP profile. External input streams remain independent of the witness;
explicit port connections do not establish circuit authentication of the stream.

`Human/Circuits/` owns row contracts, reference selection, artifact paths and named
mappings. `Human/Helpers/` owns initialized history, logical matching, public
boundaries and selected-row context; it is independent of whole-execution contracts.
Its property definitions remain the root entry point; `Core/`, `Decoder/`,
`Memory/` and `Context/` group the common review topics. Tables, delegation and
unified-machine context retain their separate groups.
`Human/Trace/` owns execution, terminal realization and composition. Three local
theorem modules retain the documented pooled proof-assembly dependency.
Explain declaration roles and parameters briefly,
with field comments for substantive assumptions. `Slop/` owns calculation
interfaces, helper lemmas, proof assembly and mechanical guards; do not add proof
prose. `Import/` has a separate fidelity boundary. Consolidate identical contracts
without hiding instruction/profile distinctions or artifact observables.

Preserve existing field scope, minimum moduli, serialized inverse conditions,
reference definitions and regression/axiom coverage. Do not change circuits,
dependencies, pins or generated artifacts as part of readability cleanup.

## Pending integration work

Follow this dependency order for coverage continuation. Simplification is complete;
preserve the integrated review contract as coverage expands.

Native-clock cuts retain raw boundary timestamps and now realize both sides in
Sail from one public initialization. Boundary reads and suffix initialization are
derived from the actual prefix state; terminal reads and recomposed transport are
checked. Two cuts also derive canonical RV32 values and bounded raw timestamps
for native worker windows, retaining complete rows, their original constraints
and exact boundary matching. The unified caller-only span interface reuses these
results. Native boundary images now retain timestamps and derive canonical seed
values from actual Sail reads; all three complete hash references consume this
interface without resetting clocks. All three references now bind selected worker
windows to actual cut states: repeated G spans in one public mode, the first
extended-BLAKE span within one ten-position controller, and the first 649-call
Keccak span. Later workers may remain outside the selected window. Native cuts
also start from retained boundary images. History derives intermediate values,
G entry controls, extended round masks and terminal agreement. Pooled and unified
instruction-boundary cuts now derive exact caller/worker request permutations,
unique slots, caller counts and full-width CSR families for these hash windows.
Cuts are aligned and follow clock two; zero-clock workers retain their actual
prefix effects. The worker-only interfaces remain available.
Unified joint instruction windows now derive actual cut states, full architectural
matching and canonical tokens with retained clocks across ordinary instructions,
callers and all four worker families. Complete machine ports and worker rows stay
in the same window; earlier unissued effects remain in the prefix. Caller-only
joint hash windows now reach all three complete references at those same actual
cut states. Shared matching projects worker boundaries and removes x0 refreshes
as Sail no-ops; entry controls and extended-round masks are derived. No independent
worker permutation or intermediate state is supplied.
Mixed-history caller regions now derive their exact instruction count from native
state matching and four-tick advancement. Public cuts inside the machine path and
a duration matching the selected worker count derive every caller selector in
the region. Worker matching and retained boundary images are then projected only
within that region; earlier ordinary effects stay in the actual joint prefix.
Public ADDI-from-x0/LUI preparation registries derive actual control reads at
each cut. Uniform, different-literal and arithmetic registries remain available;
a sequential registry also admits LW/SW, bitwise/shifts, REV8 and supported
TRIADD/XORROT interleaved with callers. Actual public decoding derives native
PC-increment selectors; native PC/clock matching identifies the final specified
literal's address. Jumps, branches and wraparound comparisons remain outside
this linear profile. State matching identifies the final ordinary row and its
accepted write, retaining its raw timestamp. Only the final preparation cycle
must be worker-free; earlier effects remain in the actual prefix. The original
extended-BLAKE first-span entry retains its separate empty prefix. No desired
read or row selector is supplied. Two preparation cuts share actual states and
the complete intervening history, with both controls derived. The aliased
TRIADD→ADDI reset derives x12 = 65537→196611→0, retaining clocks six/ten and
rejecting a fabricated read. Whole instruction retirement remains separate.
Prepared G and Keccak spans now reach their complete references at those
same mixed-history cut states even after earlier workers. Shared matching derives caller regions, worker
boundaries and actual controls; no worker masks or desired reads are supplied.
Public preparation/first-span scope, call count and duration remain explicit.
G/Keccak require homogeneity only inside the selected span; other bigint/G/Keccak
workers may precede or follow it. Extended-round workers remain outside this
mask-free scope rather than receiving an assumed mask.
Ordered finite lists of complete prepared G/Keccak spans share one continuous
native memory history. Each actual finish initializes the gap and next span;
canonical tokens, raw clocks, request bindings and every complete reference are
derived from that execution. Ordinary preparations and other nonround workers
remain in gaps; unissued prefix effects are retained. Empty windows/gaps retain
state and clocks. Public alignment/order, literal registry and each protocol's
mode/count/duration remain explicit. The regional entry below adds prepared
extended-BLAKE restarts; unrestricted protocol-shape binding remains separate.
Prepared extended-BLAKE spans now also reach complete compression at those cut
states. Raw matching and the actual LUI token derive round masks before Sail
transport, retaining the preparation timestamp. Public suffix duration derives an
uninterrupted caller region; the empty worker prefix and ten-position controller
remain explicit. Selected seven-/ten-round windows may leave later rounds outside
the window within that controller. A broader regional entry now derives masks from
raw matching inside each public LUI-prepared caller window. Every region has its
own ten-position bound; earlier workers and controller regions remain in history.
Explicit region coverage accounts for every extended-round worker before Sail
transport. Complete G/extended-BLAKE/Keccak lists then use one continuous actual
execution, retaining each span's preparation, mode/count/duration and aligned cuts.
No global empty worker prefix, homogeneous pool or ten-row pool cap is required
by that entry. Coverage and protocol shape remain explicit; broader preparation
and unrestricted protocol binding remain open.
Public caller regions now derive selected worker family and complete call count
for prepared sequences. A sequential ordinary registry and public PC/clock intervals
exclude ordinary instructions and fix the full CSR family; accepted state/request
matching derives caller participation, unique slots and equal machine/worker counts.
The public reference duration fixes each count without a selected-worker length
premise. All three complete references reuse the same continuous sequence states.
The shared extended-round controller shape/coverage remains explicit; this does
not derive unrestricted protocol validity or close invalid-call findings. COPY→ADDI,
empty regions and both bigint control gaps are checked; wrong family and inclusion
of ordinary code are rejected.
Caller cycles now connect original current-state fetch, the uniquely matched public
worker family, all actual port reads/writes, existing operation references and
Sail PC retirement at the same boundaries in one history. Prepared extended-round
cycles derive their masks first. Surplus zero-clock effects remain in the prefix;
issued bigint control gaps still admit these cycle observations. Whole custom-CSR
ABI and whole mixed execution remain separate.

1. **Hash references on subspans.** Reuse complete caller-only G, extended BLAKE and
   Keccak references for segmented spans. Derive worker boundaries, ranges,
   intermediate states and schedules from the same initialized history; retain
   public mode/span-size ABI, modeled tables and logical matching. Native-boundary
   bindings now derive G controls and extended-BLAKE round masks as well as Keccak
   controls; the public initialization entry points remain. Selected worker
   windows and their caller request spans are checked in the scopes above.
   Caller-only joint windows now bind repeated G spans in one mode and the first
   extended-BLAKE/Keccak span, retaining their existing public mode/count and prefix
   ABI. Mixed-history worker projections now derive caller regions as above.
   ADDI-from-x0/LUI preparation reaches actual control boundaries, including
   successive distinct literals in one public straight-path registry.
   Prepared G, Keccak and extended-BLAKE references are checked within the mixed
   scopes above. Preparation pairs now share one intervening native history, and
   prepared G/Keccak spans allow other nonround families outside the window.
   Arbitrary nonempty ordered prepared G/Keccak lists now compose with the actual
   intervening history in the same nonround scope. Regional raw matching now
   derives extended-BLAKE masks at each prepared restart; explicit coverage of all
   extended-round workers connects complete lists of all three references to the
   same execution. Preparation now admits arithmetic, LW/SW, bitwise/shifts, REV8
   and supported TRIADD/XORROT before its final literal, deriving native PC-increment selectors,
   actual controls and retained clocks through the same history. The aliased
   TRIADD→ADDI reset derives 65537→196611→0 and rejects a fabricated reset read.
   The public-program sequence entry now derives selected worker families/counts
   from public CSR regions and native matching, retaining shared controller-region
   coverage. Continue that controller-coverage binding, control-flow/wraparound
   and nonliteral preparation, then whole caller retirement; prefix retirement
   remains separate.
   COPY→ADDI cuts check actual control values 128→0→1 with a clock-seven seed
   retained for the second window. Extended BLAKE and Keccak completion controls
   do not restart their protocols; checked regressions forbid treating their
   windows as automatically repeating.
2. **Whole mixed caller retirement.** Use the shared caller-cycle boundaries and
   fetch to compose caller/worker spans with ordinary/custom clause retirement.
   Bind full caller ABI only where the available inputs justify it. Recover exact
   instruction/call windows and terminal PC/cells from shared history; do not
   supply intermediate states or scheduling results as premises.
3. **Native worker ROM and invalid-call binding.** Connect zero native ROM shadows
   to independent public bytes for worker operations. Resolve caller/control scope
   against available circuit inputs, retaining checked ABI gaps until justified.
4. **Remaining global boundaries.** Jump terminal-PC normalization needs richer
   teardown proof input. Inactive padding needs global state/write obligations.
   Full fetch faults, interrupts and exceptional execution require a separate
   scope and reference path.

Checked ABI gaps must remain exposed: surplus zero-clock workers without a
caller; issued bigint calls with public x12 = 0 or 65537; and a supported COPY
worker whose native ROM shadows differ from public bytes. These are logical
richer-artifact counterexamples, not whole-system or cryptographic bug claims.
Do not fix circuits or introduce assumed valid controls/nonzero invocation to
conceal them. Continue independent integration work when circuit inputs are missing.

## Deferred milestones

These require separately scoped work:

1. Extract fixed lookup rows and identities from the actual Rust setup generator,
   import them into Clean, and account for query binding, provenance and padding.
   Export/import fidelity and lookup-argument soundness remain separate.
2. Prove compiled no-cache constraints imply the richer constraints. Equivalence
   additionally needs witness extension; cached layouts and verifier helper
   expressions require their own correspondence.
3. Discharge Rust decoder/preprocessing and setup-generator correspondence.
4. Prove cryptographic lookup and memory argument soundness and connect them to
   execution claims. Keep verifier implementation refinement and protocol
   soundness as explicit downstream interfaces.
5. Prove completeness for each declared circuit relation.
6. Import and verify the actual large-field artifact and its own coefficients;
   generic prime-field proofs alone do not establish a Proth120 import.

## Verification and completion

For each coherent milestone, build the library, both executables and every
concrete `Tests/**/*.lean` module. Run the importer regressions and full axiom audit;
require no project warnings, `sorry` or project axioms. Preserve all existing
accepted/rejected fixtures and audit declarations, including axiom-free reports.
See [reproduction commands](../README.md#reproduce).

A completed change keeps arbitrary-witness claims over actual imported constraints,
explicit public assumptions and the pinned references. Its review entry identifies
observables and scope; compilation correspondence and protocol soundness are not
assumed. Update the status snapshot and commit coherent verified milestones with
Conventional Commits. Keep agent plans/audits in the gitignored `.agents/` directories.
