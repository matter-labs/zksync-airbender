# Circuit formal verification plan

Finalization of the pending integration work is active, with an hourly follow-up.
The user resumed implementation after manual review on 13 October 2026. Current
coverage, checked counterexamples and machine-check results live in
[Verification status](VERIFICATION_STATUS.md).
[Directory review guide](Airbender/Review/README.md) separates per-circuit and whole-trace reading.
[Trust and review boundaries](TRUST_AND_REVIEW.md) records provenance and unchecked
connections. Keep these documents as snapshots, without completed-work history.

## Integrated review contract

Start with the composed execution claim in
[Trace/Soundness.lean](Airbender/Review/Trace/Soundness.lean) and its
[public inputs](Airbender/Review/Helpers/Context/PooledBoundary.lean). The proof path is:

```text
public initialization → preserved write bounds → latest-write reads
                      → circuit operand bounds → original Sail execution
```

The shared `Realizes` property states execution and terminal PC/cell realization
once. Keep public conditions visible: field compatibility, platform/configuration,
initial state/program/domain, modeled tables, logical matching and unresolved
terminal conditions. Derive local bounds, reads, decoder selectors and row
interfaces inside `Proofs/`; never assume desired reads, results or decoder answers.

Use Clean's original constraint semantics and original Sail standard-instruction
clauses. Project custom operations use the pinned project specification. Keep the
unchanged-Sail discarded-load restriction distinct from the named Airbender
PC-only-NOP profile. External input streams remain independent of the witness;
explicit port connections do not establish circuit authentication of the stream.

`Review/Circuits/` owns row contracts, reference selection, artifact paths and named
mappings. `Review/Helpers/` owns initialized history, logical matching, public
boundaries and selected-row context; it is independent of whole-execution contracts.
Its property definitions remain the root entry point; `Core/`, `Decoder/`,
`Memory/` and `Context/` group the common review topics. Tables, delegation and
unified-machine context retain their separate groups.
`Review/Trace/` owns execution, terminal realization and composition. Three local
theorem modules retain the documented pooled proof-assembly dependency.
Explain declaration roles and parameters briefly,
with field comments for substantive assumptions. `Proofs/` owns calculation
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
literal's address. A separate aligned public registry adds the four original
comparisons. Accepted constraints and state matching derive modular RV32
PC/clock addresses, including comparison wraparound; modeled setup and
`4194304 ≤ p` remain explicit for this entry. An SLTIU at `0xfffffffc` followed by
ADDI at zero derives actual x12 = 65537→1→0 in the same initialized history,
retaining clocks six/ten and rejecting a fabricated read or wrong literal.
Jumps and branches remain outside both profiles. Selected public caller/controller
regions now also use modular addresses; global public round-CSR coverage remains
linear. State matching identifies the final ordinary row and its
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
Public extended-round controller regions now also derive their local worker family,
ten-position bound and exact duration from original public CSR regions, aligned
cuts and an extent of at most forty ticks. Raw matching and LUI preparation then
derive masks through the existing regional proof, before continuous reference
composition. Coverage of public decoded round CSR addresses now derives region
membership for every live extended-round worker. Raw regional matching and public
LUI preparation then derive masks for all those issued workers without supplying
global worker coverage or masks. Conversely, region membership implies live
invocation. Within this public sequential/controller profile, full worker
coverage is equivalent to the absence of zero-clock extended-round workers; this
is a proved boundary, not an added invocation premise. Global coverage remains
explicit for mask transport, with unissued workers retained in actual history.
This does not derive unrestricted protocol validity or close invalid-call findings. COPY→ADDI,
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
   from public CSR regions and native matching. Public controller extents now also
   derive local round-worker family/count/duration and the ten-position bound;
   public decoded round CSR coverage now derives all issued round-worker coverage,
   and derives their masks from raw matching/public preparation. It exposes
   zero-clock extended-round workers as the remaining global-coverage
   boundary in this profile. Comparison preparation now also derives modular
   RV32 addresses through PC wraparound, with actual SLTIU→ADDI states
   65537→1→0 and retained clocks six/ten. Continue the unissued-round boundary
   binding, jumps/branches and nonliteral preparation, then whole caller
   retirement; prefix retirement remains separate.
   Modular public caller regions now derive selected worker family/count/request
   slots through the aligned comparison profile. Modular controller regions and
   at most forty ticks derive local shape; complete prepared reference lists
   reuse the existing raw-mask/continuous-history composition. Public preparation,
   duration/cuts and global round-worker coverage remain explicit. Real comparison
   wrap excludes the ordinary reset at zero, COPY checks nonempty caller binding,
   and both bigint-control gaps plus the unissued G-prefix effect remain admitted.
   Modular global round-CSR coverage now quantifies every aligned occurrence
   between the supplied native clocks. Constraints and matching derive each
   caller's clock interval and modular address, then exact membership for live
   round workers. Public preparation and raw matching derive issued masks; full
   coverage is equivalent to absence of zero-clock round workers. Repeated-address
   guards reject covering only one occurrence. Unissued native reads now derive
   the full public initialization tokens from memory order and native write
   clocks, without a new clock-floor premise. For extended rounds, the actual
   initial x12 high limb characterizes supported exclusive masks exactly. Zero
   and multibit controls stay outside that ABI; this classifies the remaining
   unissued-round boundary without proving worker exclusion or inertness.
   The shared native x10 access now projects initialized-memory key uniqueness
   to numeric and raw invocation clocks across all four worker families,
   including zero. The unissued sublist has at most one occurrence. Two identical
   unissued G rows still pass native/request checks but fail architectural
   acceptance with a distinct seed; the single state-changing G worker remains
   admitted, and both bigint-control gaps retain the new result. Full clock
   uniqueness now groups every worker at its actual call states. A zero-clock
   worker occupies transfer clock three directly from the public initial state;
   derived machine clocks start at four and no earlier transfer exists. The
   same history reaches shared terminal cells and retains actual G→ADDI control
   states 0→1→0. Raw grouping requires no operation mask or positive invocation;
   closed realization retains the existing modeled tables and extended-round
   masks. Native memory order now also derives every machine cycle and caller
   clock, removing the extra positive initial-clock premise from the new caller
   entry. Existing entries remain available. An empty machine path at public
   clock zero still admits the state-changing unissued G worker; native boot
   remains at four. Both invalid bigint controls and LW/SW caller cycles survive.
   AUIPC now supplies a PC-relative preparation entry: the modular public
   registry and native matching derive its actual instruction address, then
   native arithmetic derives the RV32 sum with its U-immediate. Its canonical
   output token retains cut minus two and reaches the actual initialized cut
   state. Nonzero-PC and overflowing-sum fixtures retain clock six, reject a
   wrong immediate or fabricated read, and distinguish the result from the
   immediate alone. Only the final cycle is worker-free; no expected output,
   desired read or row selector is supplied. Public setup/tables and existing
   round ABI remain explicit. Literal or publicly placed AUIPC preparation now
   reaches the existing complete selected G/Keccak references and nonempty
   ordered reference lists in one continuous history. A public decoded-code
   placement policy computes the protocol entry constant; native matching and
   the canonical token derive its actual cut read. Every gap retains its native
   effects. Legacy literal signatures remain, using the same composition proof.
   Concrete G/Keccak preparation fixtures retain clock six and reject a wrong
   placement or incomplete 56/649-call window; the unissued G-prefix preparation
   remains admitted. The new modular public-region entry derives selected
   caller rows, exact request slots, worker family and count for either source,
   then reuses the same complete reference and ordered-list composition. Public
   mode/code/duration, nonround scope, domain/setup/tables and logical matching
   remain explicit. Native preparation fixtures derive empty-region counts;
   incomplete durations, cuts past the terminal and regions containing ordinary
   preparation code are rejected. Source-aware extended-round regions now also
   derive their actual round-zero seed and exclusive masks from raw initialized
   matching, for literal or AUIPC preparation. Public modular controller code
   and at most forty ticks derive family/count/duration and the ten-position
   bound. Global memory transport retains explicit full round-worker coverage.
   The legacy LUI mask/global-memory entries retain their signatures and share
   this proof. A native AUIPC fixture at PC 524288 derives x12 = 65537→524288
   and its canonical clock-six token, inhabits the empty regional/global context,
   and rejects wrong public flags and invalid cuts; two simultaneous round bits
   remain impossible under the regional ABI. The unissued G-prefix effect stays
   admitted. Source-aware public modular round-CSR occurrence coverage now
   derives precisely live regional membership and issued masks; full coverage
   remains equivalent to absence of zero-clock round workers, rather than a
   consequence of public CSR coverage alone. Complete selected G, extended-BLAKE
   and Keccak reference lists may now mix literal/AUIPC preparation in one
   continuous initialized history. Public modular caller/controller regions
   derive all selected shapes before the existing composition proof, preserving
   gaps and actual cut states. Full round-worker coverage stays explicit in the
   complete entry. Legacy coverage/reference/list signatures remain and reuse
   the same proofs. Concrete preparation/empty-region fixtures inhabit the new
   public context and reject incomplete reference counts/durations and cuts past
   the native terminal; full reference/list claims remain general accepted-witness
   theorems. Register-dependent ADDI preparation now derives its actual operand
   state from the same initialized prefix, then its RV32 result and canonical
   output token at cut minus two. Public modular code identifies the final row;
   memory induction derives operand bounds and actual native reads. Aliased
   source/destination and negative immediates are supported. Only the final cycle
   is worker-free. Native fixtures derive 65537→65665 and 65537→65536, reject a
   wrong immediate/fabricated source and retain clock six. An unissued G prefix
   derives actual control states 0→1→1, so the operand is not replaced by its
   public initial value. Legacy literal/AUIPC contracts remain and reuse shared
   arithmetic/output-token helpers. Consecutive public literal→ADDI dataflow now
   binds protocol entry constants as a third source in the existing complete
   G/extended-BLAKE/Keccak window/list composition. Raw prefix/suffix matching and
   the existing distinct public domain derive the actual source token before
   Sail transport or round-mask derivation. Only those two final cycles are
   worker-free. Native reversed-row fixtures derive 65537→127→128 and
   65537→129→128, with signed −1, aliases and canonical output clock ten; wrong
   immediates/constants, fabricated source reads and incomplete references are
   rejected. An accepted unissued G prefix remains in the same initialized
   history before literal zero and ADDI 128. This proves memory preparation and
   selected references, not full Sail retirement. Finite public register chains
   now extend literal/AUIPC roots with arbitrarily many consecutive ADDIs, across
   registers and aliases. Induction derives every canonical operand token before
   Sail/round-mask transport, sharing the legacy two-step token helper. The
   existing complete selected-reference windows/lists admit the recursive source
   under the same domain/setup/table, coverage and matching boundaries. Only
   selected preparation cycles are worker-free. Reversed-row native fixtures
   derive x12 = 127/129 → x10 = 128 → x12 = 128, actual intermediate reads and
   canonical clock fourteen; malformed immediates/constants, middle operands and
   incomplete references are rejected. Existing AUIPC roots and the actual
   unissued G-prefix effect remain inhabited. Public register dataflow now admits
   intervening arithmetic, bitwise/shift/REV8, comparison and admitted custom
   writes to other nonzero GPRs, including reads/readonly refreshes of the
   tracked register. Original
   public instruction constructors and successful decoding derive the native GPR
   destination bank/index, retaining supported shift-payload checks without
   operand bounds or instruction results. Original public decoding derives
   destination separation;
   raw initialized matching preserves its canonical word and actual timestamp
   while retaining every gap write. A final ADDI derives the fresh output before
   the existing complete selected-reference composition. No inert-gap, desired
   operand/state, bound or selector is supplied. Selected ordinary preparation cycles stay
   worker-free; caller gaps retain their workers. Native reversed-row fixtures derive
   x12 = 127/129 → gap x10 = 127/129 → x12 = 128, clock-eight refresh and
   clock-fourteen final output. A forged clock-ten source passes local native
   constraints/timestamp lookups but fails architectural matching. Constant and
   incomplete-reference guards and the actual unissued G prefix remain. Native
   ADD/SUB gaps read x12 twice, write x10 = 254/0, retain clock-nine refreshes
   and derive final x12 = 128 at clock fourteen. Wrong public destinations and
   instruction forms are rejected. A stale clock-eight source passes local
   constraints/timestamps but global token counts reject double consumption.
   Native XOR/AND gaps also retain two aliased reads, x12 = 127/129, x10 = 0/129,
   clock-nine refreshes and final x12 = 128 at clock fourteen. Wrong public
   destinations/forms, illegal shifts and discarded binary destinations are
   rejected. All four comparisons, TRIADD and the four pinned XORROT forms now
   derive their public GPR footprint without predicate bits, operands or results.
   Native SLTU/TRIADD gaps preserve x12 = 127/129, retain both readonly refreshes
   and real x10 = 0/65795 writes before final x12 = 128; the native third TRIADD
   operand is the actual old x10 = 65537. Stale sources remain locally valid and
   globally rejected; wrong public destinations/forms, unsupported MOPs and
   discarded selected destinations are rejected at the registry boundary.
   Pinned custom clauses remain unchanged; this does not assert full custom
   retirement or substitute upstream Zimop fallback. LW/SW gaps now derive the
   native GPR/RAM footprint, including the discarded-LW NOP, without supplied
   effective addresses, loaded values, store results or inert gaps. Initialized
   RAM fixtures derive x10 = 4194304→42 for LW and RAM = 42→129 for SW, retaining
   actual register/RAM refreshes and write clocks six/nine/ten. A discarded
   misaligned LW-to-x0 touches only x0; its program fails NoDiscardedLoads while
   retaining the tracked literal at clock six and RAM at clock zero. Final signed
   ADDIs derive x12 = 128 at clock fourteen. Fabricated fresh clocks and RAM reads
   pass local constraints/timestamps but fail initialized matching; wrong public
   load destinations and store sources are rejected. Original discarded-load and
   ROM-shadow boundaries remain; no original memory-clause retirement is added.
   Caller gaps now derive preservation for tracked GPRs outside x10/x12 from
   public modular ordinary-code exclusion and all four original native port
   layouts. No empty worker window, selected worker, valid control or positive
   invocation is supplied. Reversed-row literal→COPY→ADDI derives x13 = 0→127→127,
   actual COPY x12 = 128→0 and final x12 = 128 at clock fourteen; x13 retains clock
   six and the readonly x11 pointer clock eleven. A fabricated clock-eleven x13
   source passes local constraints/timestamps but fails initialized matching.
   Both invalid bigint controls retain the x11 refresh law. The existing complete
   selected-reference composition consumes the new dataflow, with unchanged
   domain/setup/table, coverage and matching boundaries. Public single-cycle bigint
   CSR regions now derive the actual returned x12 bit from native constraints and
   initialized matching, retaining its raw token at cut minus one. The native
   selected-clock floor, unique worker and family are derived. COPY-with-carry
   reads a 256-bit all-ones public RAM source and returns 192→1 at clock seven;
   COPY and both invalid controls 0/65537 retain zero returns. Return two, wrong
   family, ordinary code and cuts beyond the terminal are rejected. This does not
   validate incoming controls or execute the full CSR reference. Public ORI x12,1
   now consumes the derived zero/one return and supplies normalized one to public
   register dataflow. The byte inverse follows from the existing clock inverse;
   native lookups derive both operands and the result before Sail/round transport.
   Reversed-row COPY/carry-COPY→ORI→ADDI traces and both invalid controls derive
   actual return→1→128 with clocks seven/ten/fourteen. A fabricated clock-six
   read passes local native constraints/timestamps and fails initialized matching;
   XORI and incomplete selected-reference windows are rejected. Existing selected
   hash preparation consumes this dataflow with unchanged complete protocol scopes.
   Continue general operand-dependent x10/x12 worker results, broader operations,
   jumps/branches and whole caller retirement, retaining unsupported-control and
   unissued-worker cases.
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
4. **Remaining global boundaries.** F01 is resolved in the logical model under
   explicit canonical total-verifier boundary closure: accepted state matching
   and permutation cancellation derive the raw terminal PC bound. Cryptographic
   enforcement and Rust/artifact correspondence remain external; the original
   local counterexample remains valid. Inactive padding needs global state/write obligations.
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
See [reproduction commands](README.md#reproduce).

A completed change keeps arbitrary-witness claims over actual imported constraints,
explicit public assumptions and the pinned references. Its review entry identifies
observables and scope; compilation correspondence and protocol soundness are not
assumed. Update the status snapshot and commit coherent verified milestones with
Conventional Commits. Keep agent plans/audits in the gitignored `.agents/` directories.
