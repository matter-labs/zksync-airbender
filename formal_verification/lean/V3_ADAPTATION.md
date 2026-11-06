# V3 adaptation snapshot — 6 November 2026

## Exact sources

The current reference is [PR #585](https://github.com/matter-labs/zksync-airbender/pull/585)
at b29277dd895499574e317a994fd89243a72f06cb, based on
c1a662222cafcd96db4383dce737edb79fa62b09. GitHub head metadata and the read-only
source checkout agree. Its status reports a successful parent warm run and
explicitly leaves final full assurance pending. That is not a v2 test result.
The native v2 target remains dev 67ee094449abaebc77e58435f130ce6ea27721e5.
No Rust, dependency version or original Sail standard clause changes are imported.

[Provenance](artifacts/provenance.json) distinguishes the original 805909325
source origins from the current reference and byte-identical current reuse.
Four shared arithmetic modules and the transparent field-capacity definitions
are copied unchanged from the new source. Capacity names preserve the exact
old inequalities; they do not identify a native field. Other reused modules
retain their historical hashes and origins. The eight current architecture,
importer, finding and trust references have independent source hashes.

## Migration map

| Current v3 component | V2 connection and remaining work |
| --- | --- |
| Unified CPU local import with an explicit fixed tagged table | The v2 combined reduced circuit follows this pattern, retaining its own four-field queries, eight scalar/eight timestamp queries, original x0 decoder and log-23 placement. The regenerated native target has 117 equations and a complete fourteen-region literal pool. Both actual sign/high-byte queries follow from original Clean acceptance; universal public/physical setup and other row semantics remain open. The historical 119-equation snapshot stays separate. |
| Reduced unrolled target | This is a different multi-family assembly. The name does not make it the target for the monolithic v2 reduced JSON. Existing standalone v2 families remain reusable components. |
| Unified row semantics and initialized execution | Port the calculations against actual v2 combined selectors/operands/writes and initialized memory/state history. Standalone proofs do not discharge these native connections. |
| Compiler certificates and native CPU acceptance | Not present in this backport. The local row importer does not establish GKR cached/uncached compiler preservation, exact decoder membership or the physical verifier's argument checks. Retained stage-two JSON is opaque. |
| Worker/caller and supported-use composition | Native v2 request and initialization coordinates are retained. Issue/fulfillment accounting, worker constraints and public custom-operation ABI remain to be connected. No v3 roster or temporary semantic assumption is inherited. |
| Initialization, terminal and padding boundaries | Current v3 covers one initialization/teardown instance, possibly with several windows, under explicit matching/public premises. V2 physical initialization/teardown and terminal/padding enforcement remain open; the descriptor alone supplies none of those results. |
| Exact lookup, state, RAM and request premises | Keep their boundaries visible. Sampled products or a table-equivalence premise cannot replace the missing v2 enforcement proof. General Rust/compiler refinement, cryptographic enforcement and completeness remain separately scoped. |

## Current reduced checkpoint

[The native artifact](Airbender/Review/Circuits/ReducedMachine/Artifact.lean)
retains the complete source bytes and emits the original Clean row operations.
[Structural checks](Airbender/Proofs/ReducedMachine/ArtifactChecks.lean) retain
all six three-value queries plus their actual constant/dynamic tags and the same
fixed setup table; no disabled row, gating change or witness-supplied table data
is introduced. Existing shift/CSR request coordinates are also retained, including
its absent ABI group; unsupported profiles cannot silently carry requests.
[Intake controls](Tests/ReducedMachineImport.lean) reject altered
setup geometry, selectors, initialization/request placement and unsupported
processor/batched/indirect metadata. [Emission controls](Tests/ReducedMachineEmission.lean)
reject omitted, wrong and crossed target profiles.

The complete serial bounded pass covers 777 source/test modules, including
139 test modules; 492 existing importer controls and 44 reduced/request
controls pass, as do all seven native CLI inputs, native exporter checks,
2,306 axiom roots and all 137 public Review claims. Dependency fingerprints
retain only unchanged verified modules. Peak charged footprint was
1387.39 MiB and peak resident usage 3601.03 MiB, below the unchanged
3072/4096 MiB ceilings. Every guard completed without a live owned process.

The independent bounded provenance audit also passes: 75 legacy and five
current byte-identical sources, seven native circuits, 56 native sources,
21 setup artifacts, four exporter files, 189 v3 adaptation identities and
693 earlier v2 reuse identities. Current architecture references and
historical reuse origins match their exact Git objects. The original
checkout and dependency versions are unchanged. The combined machine has no execution
soundness theorem yet. Next: bind actual v2 reduced fixed regions and public
ROM/CSR setup, then derive combined selectors, operands, writes and original
Sail row effects before assembling initialized history and caller boundaries.
A new hourly continuation task is active at the user's request; the old task
remains paused. The unchanged-circuit policy requires documented native evidence
and explicit narrow interface assumptions for any confirmed issue.

## Renewed continuation and first fixed-region certificate

The new hourly task continues this native reduced-machine dependency chain.
[The sign/high-byte region](Airbender/Review/Circuits/ReducedMachine/Tables/SignHigh.lean)
checks all actual native rows and their tag/placement; it is a regional certificate,
not whole-setup or execution coverage. The next step is the complete native pooled
fixed relation, including actual public ROM/CSR configuration and tag isolation,
then combined row semantics. The production circuit remains unchanged. See the
[issue-handling policy](FINDINGS.md#backport-issue-handling-policy).

## Regenerated source target

The unchanged native v2 compiler produces a different target from the historical
shipped reduced JSON: 117 equations/142 variables/fourteen fixed regions rather
than 119/141/thirteen. The [active native target](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean)
and [full pool](Airbender/Review/Circuits/ReducedMachine/Tables/Native.lean) retain
that distinction and reproducible public inputs. No circuit code was fixed and
no coverage transfers through an equivalence premise. The full pool now yields
tag isolation and both actual sign/high-byte query results from Clean acceptance.
The next work is the other native operation tables, general public setup and
combined row/initialized execution, followed by workers and protocol boundaries.

The native Clean connection additionally derives all four dynamic selector
domains from exact pooled membership. Each tag comes from its actual fourth
expression and a certified stored region. The public theorem supplies no selector
answer; operation-specific identity and effects remain pending.

## Native selected shift connection

The [regenerated row claim](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now derives shift operation flags and tags from actual native equations, and
routes the register/immediate operand into the literal tag-47 truncation query.
The six explicit native packed-mask cases retain v2 encodings. Kernel equality
of stored truncation columns permits reuse of the unchanged prior row lemma;
no v3 or standalone table-equivalence premise is supplied. The selected IDs are
47/37/37/20, distinct from the standalone split-shift tables and sign-fill ID 52.
The original public-decoder connection, table-37/sign-fill meanings, shift
results/writes/PC, combined history/execution and protocol boundaries remain
pending. This is further native reduced coverage, not parity or a finding.

## Native sign-fill result

The [same native row surface](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now recovers all three minor flags and the actual tag-20 query. All 128 stored
rows yield exact filler limbs, with positive/logical and zero-shift cases
retained. The input sign and five-bit amount are derived from accepted native
queries; canonical packing derives the key bounds. This extends the regenerated
v2 combined row, with the decoded packed-mask input still explicit. It adds no
Sail retirement, full shift-result, physical setup or v3 parity claim.

The table-37 literal-column comparison requires a smaller evaluation design:
whole/sliced cross-artifact checks exceeded the existing resident or Lean
allocation limits and were terminated without survivors. The attempted draft
is excluded from coverage and committed source. No limit increase, table
assumption or circuit change was made to bypass that unfinished proof.

## Native contribution/port connection

The [native reduced claims](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now derive both actual table-37 keys/output fields, directional contribution
assembly, the actual masked destination port/address and default-PC selection.
The existing native equation-extraction and metadata-check patterns are reused
with exact prior-backport source hashes in provenance. The decoded mask remains
explicit. No table meaning, desired write or numerical PC answer is supplied as
a premise. Eight conditional native regressions and all 2,420 axiom/148 public
Review roots pass. This advances the monolithic v2 target on the v3 Unified
migration path; it does not establish table-37 arithmetic, public decoding,
initialized source reads, original shift execution or coverage parity.
