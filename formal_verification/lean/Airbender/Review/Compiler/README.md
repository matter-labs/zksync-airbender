# Compiler preservation

<!-- lean-context: Airbender.Proofs.GKRProtocol.ProgramNativeTransport.AddSubUncached -->

Start with the three [machine targets](MachineTargets.lean). Each target lists
its public setup, native acceptance and exact matching premises. The
[validation status](../../../VERIFICATION_STATUS.md#validation-evidence) records
the completed checks and the pending assurance gates.

| Target | Kernel proof |
| --- | --- |
| Unified | [Combined ordinary, modular, stream and caller execution](../../Proofs/UnifiedReduced/MachineTarget.lean). |
| UnrolledReduced | [Reduced execution with the extended-round caller](../../Proofs/Reduced/MachineTarget.lean). |
| UnrolledFullUnsigned | [Full execution with blessed split Keccak](../../Proofs/FullUnsigned/Target.lean). |

## Public program setup

The targets quantify over public text and an initial state. The
[program row function](../Helpers/Decoder/ProgramRows.lean) models native
preprocessing. It emits one masked row per text word. An unsupported word
emits the native minus-one sentinel. The
[unified row function](../Helpers/Decoder/UnifiedProgramRows.lean) includes the
combined unified registry.

Decoding runs in the public initial state. The
[decoder frame proof](../../Proofs/GKRProtocol/StatefulDecode.lean) shows that
successful decoding preserves that state. This includes the misa queries used
by multiplication and division decoding. It adds no expected-result premise.

[Public setup inputs](NativePublicSetup.lean) bind the decoder columns and
initial ROM to the supplied text. The [complete unrolled factory](NativeSubwordSetup.lean)
also replaces the program-derived subword ROM regions. Fixed helper, range
and timestamp regions keep their imported values.

The native adapters cover all 14 CPU profiles in both cache modes.
[Unrolled constraints](../../Proofs/GKRProtocol/ProgramPublicConstraints.lean)
and [unified constraints](../../Proofs/GKRProtocol/ProgramUnifiedConstraints.lean)
derive each incoming PC bound from native ranges and exact state matching.
They require no expected instruction, helper value or per-row PC premise.
The [native acceptance adapter](../../Proofs/GKRProtocol/NativeMachineAcceptance.lean)
then supplies the targets' CPU equations, execute flags and decoder matching.
Its [argument interface](NativeMachineArguments.lean) keeps the worker and
global matching assumptions explicit.

The [decoder differential](../../../scripts/check_program_decoder_rows.py)
compares the compiled Lean row function with native exports. It also compares
the circuit objects across public programs and the shared unrolled profiles.
This test binds the Lean model to each tested Rust preprocessing result.
It does not prove Rust decoder equivalence for every possible program.

## Execution premises

| Connection | Current source API |
| --- | --- |
| Cryptographic proof to native validity | Outside the logical model. Each physical row supplies its actual native base-field gate equations. |
| Physical CPU row | The actual assignment, all captured native base-field residuals equal to zero, and execute equal to one. |
| Native lookup requests | Actual native encoding fields and leaf weights select the primitive, group and setup column. Checked arithmetic transports the complete tuples to the source interpretation. |
| Exact lookup matching | Native requests match public setup rows with natural multiplicities. Sampled rational balance does not establish this premise. Physical field counters are not bound to those multiplicities. |
| Exact state and RAM matching | The stated permutations bind row boundaries and the one shared memory history. Sampled product equality does not imply a permutation. |
| Public boundaries | Initial state, text, ROM coverage, worker setup, initialization circuit, supported caller use and stream ports remain explicit. |
| Retained source constraints and execution | Native transport and exact matching derive the source equations and decoder membership. The target proofs compose those facts with the reference execution. |

[Physical bindings](../../Import/Compiler/Rows/AddSubUncached.lean) select the
captured addresses. [Native requests](../../Import/Compiler/LogicalRows/AddSubUncached.lean)
use the actual encoding fields and leaf weights. The
[transport proof](../../Proofs/GKRProtocol/ProgramNativeTransport/AddSubUncached.lean)
checks arithmetic identities, operand coverage and setup-column bindings.
[Lookup operands](LookupOperands.lean) and the [logical argument](LookupArgument.lean)
state the remaining interpretations.

Extension-field gates, compressed lookup arguments and commitment authentication
remain separate boundaries. These theorems do not prove universal correctness
of the Rust compiler.

## Compatibility claims

Earlier captured-program boundaries and whole-execution wrappers now live in
the [compatibility proof layer](../../Proofs/Compatibility/Compiler/Theorems.lean).
The original Review paths forward to those modules. Each declaration keeps its
public name, statement and proof body. All established audit roots remain.
These compatibility statements retain their original setup restrictions.
The three machine targets use the public program setup described above.

The [arithmetic API](Arithmetic.lean) and
[capture selection](../../Import/Compiler/ArithmeticInstances.lean) retain the
22 native configurations. Arithmetic extension constructs a selected gate
slice. It does not construct the complete native graph.

Artifact readers live in Import. Certificate algorithms, generated checks,
refinements and proof assembly live in Proofs.
[Compiler scope and evidence](../../../GKR_COMPILER_VERIFICATION.md) records
the validation limits and reproduction steps.
