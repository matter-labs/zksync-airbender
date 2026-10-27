# Compiler preservation

Review the [public theorems](Theorems.lean), then the definitions needed for the
selected claim. All 14 actual native row compositions and the public wrappers
compile. Program/logical execution and the final public theorem module also pass
selected-module kernel replay with a 32 MiB Lean thread stack. The final selected
3279-module/10-test frontend passes normal Lake no-build freshness and compiled
artifact-hash checks without repairs; its manifests cover only that selected
scope. Full project/executable/runtime checks, environment auditing, complete
independent replay, transitive negative controls and Linux/cold-run validation
remain pending. [Validation scope and measurements](../../../VERIFICATION_STATUS.md#current-focused-validation)
records the completed checks.

| Claim or entrypoint | Definitions to read |
| --- | --- |
| Captured native arithmetic preserves every original source arithmetic assertion. | [Arithmetic semantics and 22 configurations](Arithmetic.lean); [capture selection](../../Import/Compiler/ArithmeticInstances.lean). |
| Source arithmetic extends to a selected native arithmetic gate slice. | The same definitions; an untrusted certificate chooses the slice. This is weaker than constructing the whole native graph. |
| Pooled/unified logical execution derives lookup/helper obligations from exact native tuple matching. | [Physical row inputs](RowFrame.lean), [logical row certificates](LogicalRows.lean), [exact lookup argument](LookupArgument.lean), [pooled boundary](Pooled.lean) and [unified boundary](Unified.lean). Select pooled_logical_execution or unified_logical_execution in the public theorems. |
| Execution for a supplied program compatible with the retained decoder tables. | [Program boundaries](Program.lean). Select pooled_program_execution or unified_program_execution. |
| Supplied-program execution with Airbender's device configuration selected explicitly. | Select pooled_airbender_execution or unified_airbender_execution; the remaining handlers come from the supplied platform. |
| Compatibility execution with older framed certificates. | The older pooled_execution and unified_execution entrypoints retain [RowFrame](RowFrame.lean) and their original premises. |

## Execution premises

| Connection | Current source API |
| --- | --- |
| Accepted cryptographic proof data to native gate validity | Outside the logical model. Native base-field arithmetic remains a row-input premise. |
| Physical row input | The actual physical assignment, every captured native base-field gate residual equal to zero, and execute equal to one. The new input has no canonical source frame, source-value/count assignment, authored membership, helper-range or canonical-borrow premise. |
| Native lookup requests and transport | Requests use the actual consumed native encodings' fields and leaf weights at the physical assignment. Under full native arithmetic, checked field/mask/helper identities transport these requests to the source interpretation; operand coverage and setup-column bindings align primitive, group and setup selection. |
| Logical lookup argument | Exact matching of those native requests against independently interpreted setup rows repeated by natural multiplicities. This is supplied separately for the physical row. The final compressed/sampled rational balance does not establish exact matching, and natural multiplicities are not bound to physical field counters. |
| Authored lookup membership and helper bounds below 2^19 | Derived by the new logical composition from physical arithmetic and exact tuple matching, rather than supplied as row-certificate fields. |
| State/RAM matching and public boundaries | Exact permutations, verifier closure where applicable, public initial state/program/domain, configuration, serialized inverses and seed remain explicit. Sampled product equality alone does not imply a permutation. |
| Retained Clean constraints, decoder membership and source/trace execution | Derived by the logical entrypoints under those premises. Pooled execution additionally retains independent external-read ports. |
| Other wiring/cache and RAM-product reductions | Supporting results. The new execution connection uses actual emitted lookup tuples, while extension-field gates, sampled lookup/grand-product arguments and complete native graph semantics remain separate. |

[Physical bindings](../../Import/Compiler/Rows/AddSubUncached.lean) select actual
captured addresses and arithmetic/active predicates. The
[native request definition](../../Import/Compiler/LogicalRows/AddSubUncached.lean)
constructs nativeRequests from actual encoding fields and native leaf weights.
Its [transport and coverage proofs](../../Proofs/GKRProtocol/LogicalRows/AddSubUncached.lean)
use nativeRequests_source under full native arithmetic, nativeOperands_coverage
for primitive/group coverage, and nativeSetupColumns_binding for independent setup
columns. Source-field, mask and timestamp-helper identities are consumed by that
transport; they are not added as row-input assumptions.

[Lookup operands](LookupOperands.lean) and the [logical argument](LookupArgument.lean)
expose the remaining interpretations. The final compressed/sampled output-to-exact
matching step and physical field multiplicity binding remain an abstraction of the
global argument. The 60 final lookup-output reductions may remain standalone
supporting results. Cryptographic matching and commitment authentication are not
established. All 14 native row transport/composition modules compile and the
selected frontend regression/freshness scope passes. Full assurance remains
pending as described above.

## Program and platform scope

The retained-program wrappers still select the four-entry
[setup program](../../Data/Decoder/SelectedProgram.lean): two ADDI instructions,
a self-looping JAL and an unreachable ADD. Its MUL/DIV, shift/binop and word/subword
decoder tables are empty, so eight of twelve pooled row kinds cannot occur there.

The supplied-program wrappers quantify over a program with a structural equality
between its per-family decoder tables and those of the retained capture, together
with existing public boot/execution inputs. This equality is independent of trace
rows and supplies no per-row membership. It supports compatible supplied programs;
it does not admit arbitrary new programs or arbitrary new setup captures without
new table interpretation evidence. The generic source/trace execution layer is
already program-parametric, including branches, jumps and loops.

Generic wrappers remain polymorphic in the platform. The explicit Airbender
wrappers disable its device windows while retaining the supplied platform's other
handlers. None of these statements proves universal correctness of the Rust compiler.

The arithmetic extension theorem covers a certificate-selected subset of emitted
native gates, not necessarily every source-related gate or the whole graph. The
certificate is untrusted and its identities are checked; a valid slice does not
establish complete witness extension.

Artifact schemas/readers live in Import; certificate algorithms, generated checks,
witness construction, refinements and proof assembly live in Proofs. Their
implementation/import fidelity remains a separate review task.
[Compiler scope and evidence](../../../GKR_COMPILER_VERIFICATION.md) links current
validation limits, reproduction and historical checkpoints.
