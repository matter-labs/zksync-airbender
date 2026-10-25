# GKR compiler semantic preservation

The compiler verification effort is active. Arithmetic translation, graph wiring
and source lookup-field encoding have kernel-checked instances for all eleven
production circuit families, with and without caches. All 22 native consumer
field-role checks also pass. Source table geometry and consumed setup coordinates
are checked. Source RAM/initialization products are also checked. Literal materialized lookup tables and uniform counter witnesses are now bound
to complete native graph witnesses. RAM argument and execution composition remain open.
Source-derived timestamp/alignment query identities and their generic clock/range
semantics are checked. Source primitive/history contracts now construct valid
helper witnesses and the whole native graph in all 22 configurations.
All 60 emitted native lookup output pairs now have checked reduction proofs;
the 38 generic/range-16 groups also reduce to the original source query multiset
plus their actual setup contribution.
All 48 emitted native RAM/initialization product output scalars reduce to the
independent source tuples, preserving all 476 tuple occurrences.

## Independent source and actual compiler output

`cs/examples/export_gkr_translation.rs` builds each production `CircuitOutput`,
captures its original structured statements and Boolean variables, and then
passes that same value to the production `GKRCompiler`. No post-compilation
constraint summary supplies the source obligations. The export also retains the
complete emitted `GKRCircuitArtifact` and a separate complete-source sidecar for
the next protocol-lowering stage.

The eleven uncached outputs equal the complete retained native circuit JSONs,
including ROM table registration and unified inline initialization. Cached and
uncached compilations have identical source inputs. Source sidecars capture
lookup rows/table selectors, range checks, memory requests, delegation register
and indirect accesses, timestamp groups, machine/decoder state, substitutions,
variable layers and table sizes. Table functions remain an explicit native
interpretation boundary; their closures are not serialized.

Only `Serialize` derives were added to native source types. Compiler behavior,
dependencies and production artifact formats were not changed. The native setup
source pins include those reviewed derive changes; all thirteen retained setup
guards pass. This source-pin check is distinct from reexecuting all 25 historical
setup freshness jobs.

## Checked arithmetic claims

`GKRCompiler/Polynomial.lean` proves a computable sparse polynomial equality
checker sound over any commutative ring. `Certificate.lean` checks polynomial
ideal identities and proves backward preservation and constructive witness
extension. `Arithmetic.lean` connects those identities to original expressions,
actual native arithmetic gates and actual source-variable placements.

The untrusted Python synthesizer emits addresses, relation selections,
polynomial witness extensions and combination witnesses. It cannot supply
replacement source or lowered equations. The Lean importer reconstructs both
from the actual source/compiler pair, checks index bounds and aliasing, and
checks the native structured expression against the native sparse coefficients.
Raw BabyBear Montgomery coefficients are decoded explicitly.

For each of the 22 compilations, the public `source_preserved` theorem derives
every original arithmetic assertion and Boolean obligation from the whole
lowered arithmetic relation. The public `source_extends` theorem constructs an
assignment preserving every source variable and satisfying the **selected source
arithmetic slice**. It does not assert extension to compiler-generated memory
constraints or the complete GKR graph.

Every concrete metadata check and polynomial identity uses `decide +kernel`.
Large instances are sharded into individual checks and assembled by a proved
finite conjunction. No `sorry`, project axiom, `native_decide` or `bv_decide` is
used. The 44 instance roots, seven generic soundness roots and five rejection
controls report only `propext`, `Classical.choice` and `Quot.sound` as applicable.
They are registered in `Airbender/Checks/Axioms.lean`. Wiring, lookup-field and
additional rejection roots are registered there as well. All 140 compiler roots
passed a direct axiom audit after the corrected input-dependency replay, using
only those standard Lean axioms as applicable.

## Wiring and source lookup fields

`GKRCompiler/Wiring.lean` checks unique producers, bounded adjacent-layer reads,
cache dependencies, original source placements, the scratch-storage bijection
and complete final-output port coverage. Its importer enumerates every native
relation variant and rejects the retired batched arithmetic relation. Large
instances split individual producer, placement, gate and cache checks across
small modules. `gkr_wiring_instances.py` checks the generated scaffolding and
builds its 304 module targets strictly sequentially.

`GKRProtocol/Source.lean` types the complete semantic compiler input capture.
`SourceFields.lean` independently defines authored lookup/range requests,
decoder columns and family-mask packing, table selectors and zero padding,
with proved polynomial interpretation. `LookupImport.lean` reconstructs actual
lowered fields from the emitted circuit. The untrusted lookup certificates
provide only addresses, row selectors and polynomial-combination witnesses.
They cannot provide either side of an equality. The public
`request_fields_preserved` roots establish every reconstructed field equality
under the actual native copy equations: 4,436 fields across 836 encoded requests
in the 22 retained configurations.

Witness-evaluation metadata sometimes names an intermediate value by its
`ScratchSpace` alias. The importer resolves it through the actual reverse
mapping and checked forward inverse. An alias is interpreted as that storage
location, rather than introduced as an unconstrained additional value.

These field results are composed with concrete numerator/denominator reductions
below. RAM tuple products are connected to source tuples as described below.
Table contents, timestamp helpers and complete extension through
compiler-generated memory constraints remain required.

## Native consumer field roles

`GKRProtocol/Typing.lean` checks the field roles of every input and output against
the actual graph and its unique producer addresses. It also checks source and
scratch cells are base-field values and final outputs are extension-field
values. Every gate and cache, including assertion gates without output ports,
must appear exactly once in the ordered consumer list. `TypingImport.lean`
interprets every native relation variant explicitly and fails closed for retired
unsupported consumers. All 22 `consumer_types_valid` instances pass.

The native scalar, vector, memory and initialization flattening helpers require
distinct addresses rather than accumulating duplicate coefficients. The checker
verifies that requirement on every relevant actual gate and cache row.
`Tests/GKRConsumerTypes.lean` proves
rejection of omitted assertion consumers, changed input/output roles and
repeated flattened addresses.

`RationalSemantics.lean` additionally proves exact numerator/denominator pair
aggregation as a commutative monoid and exact multiset preservation for lookup
trees. This result does not divide by a denominator or assume a nonzero sampled
challenge. Connecting the actual native lookup trees to source requests remains
required.

## Affine cache claims

`CacheImport.lean` interprets all four actual native cache variants: scalar
lookup, vector lookup, vector setup and memory tuple. The finite descriptions
retain raw Montgomery coefficients, column order, challenge powers, address
spaces, timestamp offsets and byte-to-limb reconstruction. Each description's
input list is checked in the kernel against the separately imported cache
ports, and the complete ordered cache list is checked against the actual graph.
All 22 retained configurations pass these checks.

`CacheBindings.lean` interprets those descriptions in any commutative ring with
a homomorphism from BabyBear. `CacheSemantics.lean` proves that affine operations
commute with multilinear evaluation on the Boolean cube. For every actual
cache description, `cache_claims_bound` proves that evaluation of its canonical
row materialization equals its expected claim from dependency evaluations at
the same point. This holds for arbitrary challenge values and needs no extra
normalization or nonzero premise.

This theorem concerns the interpreted cache relation. It does not yet connect
every cache to the independently captured source requests, prove full protocol
reductions, or establish equivalence to the native witness generator's use of
preprocessed lookup mappings and padding.

`Tests/GKRCacheBindings.lean` checks actual write timestamp offsets, the PC
address space, scalar Montgomery decoding, vector family-mask packing and setup
column order. It rejects a changed dependency and a free cache claim. All 124
additional consumer/cache/aggregation roots pass a direct axiom audit using only
standard Lean axioms.

## Actual native lookup reductions

`NativeLookupImport.lean` reads the actual balanced-pair, setup, aggregate,
unbalanced-remainder and extension-copy opcodes. The original native operands
are retained separately from normalization certificates, which contain only
gate and primitive indices. `NativeLookupGate.normalization_sound` connects the
native helper formulas to exact numerator/denominator pair addition.

`LookupReduction.lean` follows actual ports through the graph. A pair read must
find the numerator and denominator components of the same checked tree.
`LookupNative/` checks all 22 configurations and all 60 emitted lookup output
pairs. BLAKE and Keccak have no separate range-16 output. Every emitted group
also passes a request-count check against its native metadata and contains
exactly one negative setup-multiplicity term. These count checks alone do not
establish original source-request identity or multiset coverage.

Large profiles use 32-step replay checkpoints. An untrusted evaluator supplies
finite checkpoint states; Lean checks each transition against the actual
instructions and composes the proved state invariant. BLAKE-round stays below
the existing 2560 MiB physical memory cap. No compiler traces are altered.

`BaseEncoding.lean` and `AffineExpansion.lean` provide the remaining connection's
generic foundation: selected actual definitions preserve affine interpretation,
base-column identities lift through a field homomorphism, and vector encoding
preserves those identities for arbitrary alpha. A base-role check prevents an
extension-field vector cache from being treated as a free base column. Concrete
source labels and column identities are checked and composed with these native
reduction roots as described below.

The lookup graph and base-encoding controls reject swapped/mixed pair
components, missing copies, dropped/repeated source labels, invalid native gate
or definition indices, wrong operand weights and replacement payloads. The
combined 534 compiler roots pass a direct axiom audit with only standard Lean
axioms. This audit is separate from the historical full-project assurance gates.

## Consumed operands and original source queries

`LookupSourceData.lean` enumerates actual consumer operands and actual affine
definitions. `LookupSourceImport.lean` expands selected copy/cache/materializer
heads and checks the result against the separately imported native registry.
Selectors contain only actual definition indices, source row indices and
polynomial-combination witnesses. Both sides of every column identity are
reconstructed from actual native columns and independently captured source
fields. A checked address-bank round trip prevents an arbitrary projection from
discarding a native input. Decoder masks receive their own base-role and source
identity checks.

All 4,436 consumed authored fields pass these checks in the 22 configurations.
For each of the 38 emitted generic/range-16 groups, `native.genericSourceReduction`
or `native.range16SourceReduction` composes the per-query identities with the
actual reduction root. Expected query lists are reconstructed in original source
order, independently from the consumed operand selectors. Kernel-checked exact
label permutations preserve every occurrence, including duplicate queries and
the decoder request. The theorem holds for arbitrary challenges, under the
actual affine-definition, base-copy and native lookup equations.

The resulting sum contains the original source queries and one **actual native
setup contribution**. This boundary is explicit: the theorem does not yet
identify that contribution with independently interpreted source table contents.
The 22 timestamp groups still require their independent source-helper
derivation. These are required before claiming complete compiler preservation.
Large BLAKE-round instances split operand proofs into 32-operand modules, then
compose the checked results; the bounded builder processes these sequentially.

`Tests/GKRLookupSource.lean` rejects an unretained actual column, an omitted
decoder occurrence and a query replaced by a second setup occurrence. The
combined 658 compiler roots pass a direct axiom audit using only standard Lean
axioms. This audit remains separate from full-project assurance gates.

## Source table geometry and setup interpretation

`TableImport.lean` reads the original source table sizes and compilation
configuration independently of the native layout. All 22 configurations pass
kernel checks of every table offset, the decoder boundary, total table extent,
trace length, encoded width and table-selector presence. Source table-size sums
also agree with the captured table driver total.

Each of the 60 actual setup operands has the expected ordered setup columns:
generic columns, the virtual range-16 column or the virtual timestamp column.
Its multiplicity comes from the corresponding declared base-field witness
column. These columns are pairwise distinct and do not alias any original source
variable. The checked affine expansion includes cached setup vectors.

For each generic/range-16 group, `native.genericSourceTableReduction` or
`native.range16SourceTableReduction` now replaces the remaining native setup leaf
with a source setup-row interpretation. The output equals the exact original
query sum plus the negative source multiplicity/table contribution. This holds
for arbitrary challenges, under explicit agreement of the supplied table values
and multiplicity with their assigned input cells. Table functions/program
contents and multiplicity generation remain an interpretation interface; this
result does not establish native witness-generator equivalence or derive lookup
membership from an algebraic fingerprint.

The table controls reject changed offsets/decoder boundaries, reversed generic
columns, the wrong virtual range column and a multiplicity aliasing an original
variable. The combined 1,010 compiler roots pass a direct standard-axiom audit.

## Actual native memory and initialization products

`NativeProductImport.lean` reads every actual cached/uncached memory pair,
materialized memory term, product aggregation, mask, extension copy and
initialization/teardown pair. Memory caches retain their actual affine input
addresses. Initialization tuples preserve RAM address space, virtual setup
columns, set-index high-address offsets and teardown timestamp/value columns.
Retired product consumers fail closed.

`ProductReduction.lean` follows actual ports and retains mask addresses in the
formula. All 22 configurations pass, covering 48 output scalars: RAM read/write
for every compilation and inline initialization/teardown read/write for both
unified configurations. Each RAM output has exactly one final mask around its
tuple product; initialization outputs are unmasked. Leaf counts agree with the
native request/teardown metadata. These counts do not establish source tuple
identity or source multiset coverage.

Each 32-step checkpoint is a finite literal checked by kernel reduction against
the actual normalized instructions. The final product theorem is exact for
arbitrary challenge and mask values. The separate mask-distribution lemma
requires an idempotent mask explicitly; the concrete final-mask shape does not
need that extra premise.

`Tests/GKRNativeProduct.lean` checks actual initialization RAM tags and set
offsets and rejects missing dependencies/copies, invalid gate/primitive indices,
changed mask sources, non-Boolean mask distribution and exchanged read/write
leaf bags. The combined 1,293 compiler roots pass the direct standard-axiom audit.
The source-tuple connection is established by the following additional stage;
timestamp/alignment helpers and complete witness extension remain required.

## Independent source memory products

`MemoryRequests.lean` derives read/write tuples from the original executor or
delegation inputs. It retains address spaces, byte-to-limb reconstruction,
constant and variable indirect offsets, local write timestamps, PC markers and
delegation markers. Initialization writes the zero state; teardown consumes the
final state. Initialization geometry comes from the source configuration and
the explicit two-bit word-width compile parameter, checked against the actual
native initialization metadata.

`MemorySource.lean` separates original source variables from history timestamps
and initialization/teardown inputs. The concrete projection into actual native
input cells has checked bounds, address-bank membership and base-field roles.
History slots follow source request order; they are not additional original
source variables. The memory-history validity of these inputs remains an
explicit boundary for the next helper/witness-construction stage.

`MemoryCertificate.lean` checks each complete seven-field fingerprint identity.
It reflects the actual consumed operand after selected actual affine/cache
definitions and compares it with the independently constructed source tuple.
Formal challenge coordinates are separate from all base-field input cells.
`HomPolynomial.lean` proves that these checked polynomial identities hold after
mapping BabyBear into any commutative extension ring, for arbitrary challenges.
Certificates supply only addresses, occurrence/definition selectors and
copy-ideal witnesses; they cannot supply either equation.

All 22 `MemoryNative/` instances pass. The 48 `SourceReduction` roots compose
these identities with the actual native product reductions, preserving exactly
476 read/write/initialization occurrences. Exact label permutations preserve
multiplicity even when common-subexpression elimination shares a native factor.
The RAM execution mask is proved equal to the original source predicate under
actual base-copy equations; the final-mask shape requires no additional Boolean
assumption. Initialization products are unmasked.

`Tests/GKRMemorySource.lean` rejects changed address spaces, consumed payloads,
timestamp limb order, unexpanded extension caches, lookup challenges in memory
encoding, dangling source/history references and replaced execution predicates.
It also checks initialization direction and shared-factor multiplicity.
These are exact algebraic fingerprint results, separate from cryptographic
product matching and memory-history soundness.
The combined 1,700 compiler roots pass the direct axiom audit using only
`propext`, `Classical.choice` and `Quot.sound` as applicable.

## Source clock and alignment helpers

`HelperSource.lean` derives all timestamp range queries from the original
executor/delegation state and memory operations. These include executor final
clock limbs, the delegation invocation-clock quotient, borrowed read/write
comparisons and inverse-power indirect-address alignment. Borrow witnesses have
a third domain, distinct from original variables and memory-history inputs.
All 22 current source profiles have no relative read-timestamp groups; the
importer rejects grouped profiles pending a separate proof.

`HelperImport.lean` connects these independently derived fields to the actual
consumed native lookup operands after checked affine expansion. It checks the
original/history projection, base-field roles, distinct borrows, borrow
freshness and exact source-query occurrence coverage. All 22 instances pass,
covering 474 query occurrences. Their `timestampSourceReduction` roots compose
with the actual native lookup output reductions, retaining the actual setup
contribution. This completes source-query reductions for all 60 native lookup
output pairs. The materialized setup and counter construction below now binds
those setup values and multiplicities to the complete native graph.

`HelperSemantics.lean` proves that the two borrowed range expressions imply
strict integer timestamp order and constructs a Boolean borrow and both range
bounds from that order. It proves alignment soundness and completeness under
the checked field-capacity condition, and derives the added executor arithmetic
assertions from integer clock advance by four. It reuses the existing two-limb
clock soundness theorem. No compiled helper assertion or range condition is a
premise of these completeness lemmas. `HelperAssertions.lean` independently
identifies the added clock/borrow assertions for the full arithmetic stage.

`Tests/GKRHelperSources.lean` rejects changed borrow dependencies, coefficients,
clock fields and dangling borrow references, non-Boolean borrows, unsupported
alignment capacity, unaligned pointers and a changed clock step. It also checks
the constructive borrow/alignment lemmas and original-column separation.
The combined 1,988 compiler roots pass the direct standard-axiom audit.
Full native witness construction, including composition of these helper facts
with every emitted arithmetic assertion, remains required.

## Complete base-field arithmetic

All 22 complete base-field arithmetic instances pass. The importer reconstructs
every base-field gate, scalar cache and scalar materializer. Its source consists
of the original equations/Boolean obligations and independently derived
clock/borrow assertions. `full_arithmetic_preserved` derives all these source
obligations from the full native base-field relation;
`full_arithmetic_extends` constructs a witness for that entire relation under
those obligations. `full_arithmetic_equivalent` combines both directions.
The following additional stage constructs the extension-field graph and
discharges these arithmetic helper assertions from a source clock contract.

The finite input domain preserves original logical variables, including those
placed in computed base-field cells, and explicit auxiliary input columns.
Those coordinates form an initial segment of the native bank, so their
preservation follows structurally. The certificate supplies only computed
extension polynomials and ideal witnesses; it cannot replace a source or native
equation. Distinct-address, forward and backward checks are split into modules
of at most 32 cases and assembled with proved finite conjunctions. This avoids
retaining the whole large BLAKE-round reduction in one kernel job.

The instances cover 2,191 native relations, 1,870 source equations (including
240 independently reconstructed helper assertions), and 3,914 logical/auxiliary
input coordinates. All 2,229 combined compiler audit roots report only standard
Lean axioms. Five concrete controls check a changed computed value, a dropped
borrow assertion, derivation of the borrow bit from accepted native arithmetic,
and preservation of the actual input addresses. A separate freshness control
zeros the actual native borrow assertion while retaining the source; normal Lake
rebuilding rejects its backward identity, and restoration passes.

## Whole native graph and source contracts

All 22 configurations have a canonical witness for every emitted base-field
relation, affine definition, lookup operation and memory/initialization product
operation. The instances cover 2,681 extension steps, 363 base affine definitions,
1,616 native lookup operations and 780 native product operations. Extension
copies occur in both semantic operation lists and have one physical write.

`Functional.lean` proves execution and preservation of earlier relations for a
program with fresh extension outputs and available inputs. Each actual step's
field roles, unique outputs and dependencies are kernel checked. Operations
evaluate all right-hand sides before writing their outputs. This construction
uses no division or nonzero-challenge premise. `BaseAffine.lean` connects each
base affine definition to its actual complete-arithmetic relation; these
definitions are derived from accepted base arithmetic rather than assumed.

`FunctionalLinksImport.lean` derives physical copy equations from complete base
arithmetic, transports them to the existing source-model coordinate banks, and
checks equality of the actual affine-definition inventories. Its canonical
typed assignment therefore satisfies the source-output reductions: all 60
lookup pairs and all 48 RAM/initialization scalars retain their independently
captured source formulas. No native lookup/product/cache/copy equation is an
additional premise of these canonical-output theorems.

`SourceContractImport.lean` separates original source equations from the added
clock and borrow assertions. Kernel scope checks prove that fresh borrow
coordinates cannot change original equations or clock expressions. Canonical
borrows are Boolean; the added clock assertions follow from bounded integer
timestamps and advance by four in the original executor state. Worker profiles
without an executor state require no such clock-advance premise. Thus
`source_contract_graph_extends` constructs the whole graph from original source
arithmetic and this source clock contract. It preserves all coordinates outside
the fresh borrow set, including all 3,286 original logical coordinates across
the two cache modes.

This construction establishes the emitted gate equations and their source
output formulas. The later source-primitive and materialized-table stages
construct valid helper histories and lookup counters. RAM argument composition
remains open. Inactive histories require a canonical witness where helpers are
unconditional; preserving arbitrary inactive history cells does not establish
argument acceptance.

Five actual ADD/SUB controls reject duplicate extension writes, missing
dependencies, overwriting base cells and a changed base affine recipe, and
check lookup construction at zero challenges. The combined 4,482-root axiom
report is checked separately from full independent kernel replay.

## Source primitive and inactive-history witnesses

`HistoryErasureImport.lean` derives history coordinates from original memory
requests, then checks that erasing them preserves the original arithmetic and
added clock equations. Current clocks, execution flags and alignment pointers
are also preserved. Executor histories include original logical columns;
worker histories use separate compiler inputs. Their distinction is retained.

`HelperValidity.lean` derives all helper range memberships from source integer
conditions: bounded and strictly ordered active timestamps, positive bounded
current timestamps on padding rows, worker clock phase, and aligned 16-bit
pointer limbs. These premises contain no compiled helper query or lookup
equation. Zero is a valid canonical inactive history under the positivity
condition. Native executor clocks, including padding, start at 4; see
`common_constants/src/timestamps.rs` and the padding convention in
`prover/src/gkr/witness_gen/family_circuits/mod.rs`. This implementation evidence
does not replace the explicit source clock premise of the Lean theorem.

`HelperValidityImport.lean` checks the exact helper inventory and its physical
coordinate transport to the emitted native operands. `helper_graph_extends`
constructs the whole native graph and proves membership of all 474 helper query
occurrences in the 19-bit range, for all 22 configurations. Fresh canonical
borrows preserve original coordinates; active histories are retained verbatim.
On inactive rows only the checked history coordinates may also change. The
generic masking theorem preserves every masked fingerprint under that history
change, for arbitrary challenges.

Four controls reject erasing a current clock or aliasing a borrow with it,
exhibit failure of zero history at clock zero, and check inactive masked-effect
preservation. Large transport checks are proved per field and assembled by
`BoolChecks`, keeping the same resource limits as the preceding stages.

## Materialized lookup traces and uniform counters

`Airbender/Data/GKRSetup` imports all physical setup columns, scalar range
columns, regions and program data from the eleven retained setup artifacts.
The importer preserves the parsed literal data; chunking changes only the Lean
representation. Generated literal-helper editor metadata is omitted, while
normal elaboration diagnostics and kernel checking remain enabled. Existing
Airbender input dependencies track these setup JSON files.

`MaterializedNative` binds both cache modes to that family's actual table data,
trace domain, width, fixed-region offsets and retained uncached circuit bytes.
`MaterializedRangeNative` proves that the actual affine prefixes contain every
16-bit and 19-bit value. Its proofs stay symbolic over the trace domain.

`CounterFrameNative` checks the actual multiplicity coordinates, their freshness
and their disjointness from source equations and helper fields. All consumed
lookup setup addresses are checked outside the complete finite arithmetic bank;
`OracleFrameNative` binds them through the external base-value interface.
A default placement index is never accepted as an external setup coordinate.
`QueryFrameNative` checks that history normalization, fresh borrows and counters
preserve all authored query fields and masks, including their actual physical
transport. All 22 configurations pass these checks.

`UniformCounters` and `GroupedTrace` construct one base-field multiplicity vector
**before** the extension ring or challenges are chosen. Repeated and weighted
query occurrences are retained. Disabled queries need no table-row witness.
The exact rational-pair numerator is zero even at zero denominators; no inverse
or nonzero-challenge premise is used for this polynomial identity.

Every `MaterializedWitnessNative.native_lookup_trace_extends` instance now takes
original source arithmetic/Booleans, the bounded source clock contract, source
ordering/alignment conditions and membership of enabled authored requests in the
materialized source table. It constructs that uniform counter vector and, for
each ring/challenge interpretation, complete native base/extension graph
witnesses for every row. The witnesses contain the selected counters and actual
setup rows, preserve the original authored requests, and retain all helper range
memberships. Their **actual native lookup output ports** have zero aggregate
rational-pair numerators for every emitted lookup group. All 22 instances pass.
This is the exact polynomial aggregate, separate from verifier division and
cryptographic soundness.

Ten regression controls cover repeated-query cancellation, an incorrect count,
zero denominators, a disabled unmatched query, a setup/input misclassification,
source-coordinate aliasing, actual range membership and a timestamp endpoint, a query that reads
normalized history and an incorrect source projection. The normal root build,
controls and exact combined 4,482-root axiom audit pass, with only the standard
Lean axioms. Source/compiler and lookup certificate provenance checks also pass.
The constructive RAM/initialization frame and final execution composition remain
open; these lookup results do not assert RAM argument acceptance.

## Connection to the retained Clean models

`CleanArithmeticImport.lean` reconstructs the exact Clean expression trees for
the actual post-compiler structured statements, using the existing signed
BabyBear coefficient interpretation. Ideal witnesses against the complete native
base-field relation prove all 2,070 assertions across the 22 configurations.
The source assertions and both sides of each polynomial equality come from the
actual artifact; the certificate supplies only ideal witnesses.

Each logical placement is checked against the actual native address bank.
The exact placement keys equal a consecutive range, and every arithmetic
expression stays within that range. No used arithmetic variable falls through
the projection's default case. Individual physical checks keep large profiles
within the existing memory limits.

`CleanLinksNative` checks that these assertion lists equal the arithmetic in
each existing circuit model's `importedConstraints` and full `clockConstraints`.
Both cache modes therefore feed the same retained model through their own actual
physical placements. The resulting constraint theorems take explicit primitive
lookup-membership premises; they do not derive those memberships from sampled
lookup-output equalities. ROM/setup tables retain their existing arbitrary
interface parameters. Binding source queries and helper ranges to those
memberships and composing the global execution relation remain further work.

Two actual ADD/SUB controls reject replacing a retained Clean expression and
changing its logical placement. These checks, the complete native arithmetic
replay, the model-list equalities and the combined axiom audit are separate
validation steps.

## Reproduction and freshness

The materialized stages are registered in `gkr_checkpoint.py`: full setup,
table bindings, counter and oracle frames, query frames, scalar ranges and
complete trace witnesses. Run stages within the existing bounded worker;
`gkr_query_frame_instances.py` also selects a family/cache mode. The BLAKE round
query proofs use 64-field modules and exact final coverage, so normal Lake
replay retains completed chunks when a run reaches its time budget.

`audit_gkr_compiler_axioms.py` reads the exact registered 4,482-root inventory
from `Airbender/Checks/Axioms.lean`, builds its imports sequentially and checks
every report and permitted axiom. The checkpoint's `audit` stage invokes it.
Keep axiom reports and full independent kernel replay distinct.

Run heavy commands one at a time through the repository's bounded worker,
with the existing 2560 MiB physical / 5120 MiB resident / 900 second limits.
Incremental reruns resume successfully checked modules after a time checkpoint.

```sh
# Inside formal_verification/lean; wrap each command with scripts/bounded_fv.py.
python3 scripts/export_gkr_translations.py
python3 scripts/check_gkr_translations.py
python3 scripts/gkr_wiring_instances.py --build
python3 scripts/export_gkr_lookup_certificates.py
python3 scripts/check_gkr_lookup_certificates.py
python3 scripts/gkr_lookup_instances.py
python3 scripts/gkr_lookup_source_certificate.py --check
python3 scripts/gkr_consumer_instances.py --stage source
python3 scripts/gkr_table_instances.py --check --build
python3 scripts/gkr_product_instances.py --check --build
python3 scripts/gkr_memory_certificate.py --check --build
python3 scripts/gkr_helper_instances.py --check --build
python3 scripts/gkr_full_arithmetic_certificate.py --check --build
python3 scripts/gkr_functional_instances.py --check --build
python3 scripts/gkr_functional_links.py --check --build
python3 scripts/gkr_source_contract_instances.py --check --build
python3 scripts/gkr_history_erasure_instances.py --check --build
python3 scripts/gkr_helper_validity_instances.py --check --build
python3 scripts/gkr_clean_arithmetic.py --check --build
python3 scripts/gkr_clean_links.py --check --build
LEAN_NUM_THREADS=1 lake --no-cache build +Tests.GKRHelperValidity:olean
LEAN_NUM_THREADS=1 lake --no-cache build +Tests.GKRCleanArithmetic:olean
LEAN_NUM_THREADS=1 lake --no-cache build +Tests.GKRCompilerCertificate:olean
LEAN_NUM_THREADS=1 lake --no-cache build +Tests.GKRCompilerWiring:olean
LEAN_NUM_THREADS=1 lake --no-cache build +Tests.GKRLookupFields:olean
```

The manifest binds producer scripts, exporter, Rust toolchain, Cargo lock,
native source provenance and every pair, certificate and complete-source
sidecar. The guard resynthesizes identities, checks source coverage and cache
agreement, compares complete native outputs and checks Lake's explicit input
dependencies. Exporters preserve identical file bytes and modification times.
The libraries use Lake's `needs` keys to fetch the actual input-file facets.
The deprecated `extraDepTargets` configuration fetched target declarations with
empty traces for these input files; an actual mutation control exposed that
gap. It has been replaced for the existing Airbender library and both compiler
libraries. The same bounded workflow must replay affected targets normally.
Hash agreement or successful synthesis alone is not kernel verification.

`test_gkr_lookup_freshness.py --work-dir /tmp/FRESH-DIRECTORY` builds an isolated
proof using the locked local package closure, changes an actual native lookup
coefficient while preserving the authored source and certificate, checks that
normal Lake rebuilding reaches a kernel rejection, then restores and rechecks.
It never changes retained repository artifacts or copies compiler build traces.
With `--stage consumed`, the control changes only an actual consumed query
operand, preserving the authored source and request metadata. Normal
Lake invalidation reaches rejection in the source-operand bridge; restoration
rebuilds successfully.
With `--stage memory`, the same isolated control changes an actual memory
cache's timestamp offset while retaining the source, ports and certificate.
The source-memory fingerprint checker must reject the rebuilt proof.
With `--stage helper`, it changes the consumed low-comparison cache coefficient
while retaining the source and timestamp query metadata; the source-helper
checker must reject the dependency-aware rebuild.
With `--stage full_arithmetic`, it zeros an actual native borrow assertion while
retaining the original source and helper-query metadata. The complete arithmetic
checker must reject the dependency-aware rebuild.

`Tests/GKRCompilerCertificate.lean` starts from the actual ADD/SUB translation
and proves rejection of dropped constraints, a changed coefficient, a wrong
placement, a wrong witness extension and inconsistent native sparse/structured
fields.

Additional kernel controls reject wrong layers, out-of-range memory ports,
cache-layer errors, duplicate producers/placements, dangling output ports and
stale producer tables; lookup controls reject changed table selectors, padding,
decoder masks, scratch aliases, authored fields and source projection.

## Required remaining work

1. Frame source RAM/initialization values through canonical histories, borrows,
   counters and external base inputs. The existing native product reductions
   must compose with the same complete graph witnesses as the lookup result.
2. Compose those source memory products with the global pooled argument.
   Materialized lookup tables, uniform counters and actual lookup output
   aggregates are now checked in all 22 configurations.
3. Discharge the retained Clean model's primitive lookup premises from the
   source-query/helper proofs, then compose with existing circuit/execution
   roots. Its complete arithmetic lists are now connected to the native relation.
4. Keep algebraic fingerprint preservation separate from cryptographic
   soundness. A sampled product equality alone cannot establish exact lookup or
   RAM membership.

This is instance translation validation of actual production compiler runs,
backed by generic checker-soundness theorems. It is not a proof of the Rust
compiler for every possible `CircuitOutput`.
