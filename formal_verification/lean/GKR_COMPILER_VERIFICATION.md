# GKR compiler semantic preservation

The compiler verification effort is active. Arithmetic translation, graph wiring
and source lookup-field encoding have kernel-checked instances for all eleven
production circuit families, with and without caches. Full protocol reduction,
RAM/timestamp lowering, cache binding and complete witness extension remain open.

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

These results cover the visible request fields and structural output ports.
They do not yet establish correct numerator/denominator reductions, RAM tuple
products, base/extension field roles, cache binding, output-group semantics or
complete extension through compiler-generated memory constraints. The generic
lookup-pair/product-fold algebra in `GKRCompiler/Reduction.lean` is checked but
still needs those concrete graph connections.

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

`Tests/GKRCompilerCertificate.lean` starts from the actual ADD/SUB translation
and proves rejection of dropped constraints, a changed coefficient, a wrong
placement, a wrong witness extension and inconsistent native sparse/structured
fields.

Additional kernel controls reject wrong layers, out-of-range memory ports,
cache-layer errors, duplicate producers/placements, dangling output ports and
stale producer tables; lookup controls reject changed table selectors, padding,
decoder masks, scratch aliases, authored fields and source projection.

## Required remaining work

1. Connect checked wiring to actual base/extension field roles and native
   consumer formulas; certify cache materialization and binding.
2. Derive lookup/range/decoder and RAM/timestamp obligations from the captured
   source inputs; certify their actual gate reductions and helper formulas.
3. Prove complete witness extension under explicit source primitive-query and
   memory-history contracts, then compose with existing circuit/execution roots.
4. Keep algebraic fingerprint preservation separate from cryptographic
   soundness. A sampled product equality alone cannot establish exact lookup or
   RAM membership.

This is instance translation validation of actual production compiler runs,
backed by generic checker-soundness theorems. It is not a proof of the Rust
compiler for every possible `CircuitOutput`.
