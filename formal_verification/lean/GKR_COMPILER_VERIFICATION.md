# GKR compiler semantic preservation

The compiler verification effort is active. Arithmetic translation, graph wiring
and source lookup-field encoding have kernel-checked instances for all eleven
production circuit families, with and without caches. All 22 native consumer
field-role checks also pass. Full protocol reduction, RAM/timestamp lowering,
setup interpretation and complete witness extension remain open.
All 60 emitted native lookup output pairs now have checked reduction proofs;
the 38 generic/range-16 groups also reduce to the original source query multiset
plus their actual setup contribution.

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
below. RAM tuple products, table contents, timestamp helpers and complete
extension through compiler-generated memory constraints remain required.

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

## Reproduction and freshness

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

`Tests/GKRCompilerCertificate.lean` starts from the actual ADD/SUB translation
and proves rejection of dropped constraints, a changed coefficient, a wrong
placement, a wrong witness extension and inconsistent native sparse/structured
fields.

Additional kernel controls reject wrong layers, out-of-range memory ports,
cache-layer errors, duplicate producers/placements, dangling output ports and
stale producer tables; lookup controls reject changed table selectors, padding,
decoder masks, scratch aliases, authored fields and source projection.

## Required remaining work

1. Connect lookup setup contributions to the source table layout and contents.
2. Derive timestamp and RAM/alignment helper obligations from the captured
   source inputs; certify their actual gate reductions, tuple identities and
   complete product groups.
3. Prove complete witness extension under explicit source primitive-query and
   memory-history contracts, then compose with existing circuit/execution roots.
4. Keep algebraic fingerprint preservation separate from cryptographic
   soundness. A sampled product equality alone cannot establish exact lookup or
   RAM membership.

This is instance translation validation of actual production compiler runs,
backed by generic checker-soundness theorems. It is not a proof of the Rust
compiler for every possible `CircuitOutput`.
