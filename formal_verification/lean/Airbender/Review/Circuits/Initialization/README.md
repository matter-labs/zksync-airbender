# Initialization and teardown

[The public soundness claims](Theorems.lean) connect the actual standalone and
unified inline GKR outputs to products of existing memory-history tokens. The
[execution adapters](../../Trace/Initialization.lean) use those computed tokens
in pooled and unified execution, deriving the native zero seed instead of
requiring a caller-supplied circuit-to-token correspondence.

## Review surface

- [Model](Model.lean): native pair, product and extension-copy gate meanings;
  six weighted address/time/value limbs and the unweighted RAM space constant.
- [Artifacts](Artifact.lean): imported geometry, scalar columns, producer graph
  and output mapping. Standalone has 14 gates, eight sets and 2^24 rows; inline
  has eight selected gates, two sets and 2^23 rows.
- [Products](Products.lean): symbolic full-domain token lists and output products.
- [Boundary](Boundary.lean): public distinct window selection and computed native
  initial/terminal memory lists. Register teardown is an explicit separate boundary.
- [Pooled inputs](../../Helpers/Context/InitializationInputs.lean) and
  [unified inputs](../../Helpers/Context/InitializationUnifiedInputs.lean): retained
  public Sail/program/configuration/table and starting PC/clock conditions.

The [importer](../../../Import/Initialization.lean) follows the actual designated
outputs, including producers stored in the externally connected gate arrays.
Unsupported required relations or input banks, caches, missing/duplicate
producers, cycles, wrong teardown columns and swapped output phases fail import.
The inline RAM roots are output offsets 8/9, separate from ordinary memory's 6/7.
The terminal product comes first in both native output mappings.

## Proved and retained boundaries

Gate satisfaction on every native row implies the exact encoded products.
The [proof implementation](../../../Proofs/Initialization/Native.lean) checks imported wiring
and complete leaf coverage, rearranges symbolic products, and derives address
geometry, distinct/aligned cells, register coverage and the zero native seed.
Terminal tokens retain the actual raw timestamp/value columns. No local 16-bit
range check is invented. Zero ROM-shadow tokens remain separate from public
Sail program bytes.

Distinct window indices remain an explicit statement-validation interface;
sparse and reversed distinct selections are allowed. Public register boundaries,
Sail initial profile, code/configuration, setup binding, native gate satisfaction
and exact logical matching remain explicit. The adapters do not derive logical
token permutations from sampled product equality. Parsing/emission fidelity,
Rust/GKR evaluation refinement and cryptographic enforcement remain external.
The existing full mixed-worker execution result is unchanged.

[Proof fixtures](../../../../Tests/Initialization.lean) establish acceptance for
all rows of both actual graphs, reject a wrong root, distinguish the two phases,
check endpoint geometry and retain an accepted raw value limb 65,537.
[Importer regressions](../../../../Tests/InitializationImport.lean) compare the
emitted graph with parsed source bytes and reject malformed dependencies,
columns, virtual inputs and output mappings. Full row domains stay symbolic;
native module initialization never allocates their token lists or products.
