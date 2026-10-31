# GKR compiler semantic preservation

<!-- source-names: keccak_special5 -->

For human review, start with the [compiler entrypoints and their definitions](Airbender/Review/Compiler/README.md).
Readers and capture bindings are under `Airbender/Import`; supporting calculations
and generated certificates are under `Airbender/Proofs`. This guide records
current scope and validation limits. The
[historical record](GKR_COMPILER_VERIFICATION_HISTORY.md) retains detailed
implementation stages, intermediate APIs and checkpoint evidence.

## Current scope and validation limits

The restored hash circuits have known gaps covered by the explicit
[F11 hash witness contracts](FINDINGS.md#f11--hash-witness-contracts-remain-unenforced).
Those are private-witness assumptions, not native enforcement or public-input
validation. Production circuit changes made only to make proofs succeed are outside this effort.
The [supported-use trace entrypoint](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean)
instead derives the bigint/hash worker contracts from public program safety and
exact native prefixes for bigint, G and extended round.

The three [machine targets](Airbender/Review/Compiler/MachineTargets.lean) are
proved. The full unsigned target includes the blessed 361-call split Keccak
sequence. Its [proof](Airbender/Proofs/FullUnsigned/Target.lean) uses the three
rebased split layouts and their derived borrow equations. It excludes
`keccak_special5`. Unified and reduced use their own supported caller registries.
The [earlier coverage finding](FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage)
records the historical gap and the current validation boundary.

For 22 captured cached/uncached compilations, base-field arithmetic preservation
is proved. Wiring/cache checks, 60 lookup-output reductions and 48 RAM-product
reductions are supporting results. Physical-row logical execution entrypoints
use only the actual physical assignment, native base-field arithmetic and an
active row, plus exact native lookup-tuple matching. Native requests are built
from consumed native encoding fields and leaf weights at the physical assignment.
Checked field/mask/helper identities under full native arithmetic transport them
to source operands; native operand coverage and independent setup-column bindings
connect primitive/group/setup selection. Their composition derives authored
membership, helper bounds, Clean validity and decoder membership without canonical
source/borrow framing. Exact state/RAM permutations and public
boundaries/seed remain explicit. Older framed entrypoints remain compatible.

The [logical lookup argument](Airbender/Review/Compiler/LookupArgument.lean)
uses natural multiplicities. The remaining final compressed/sampled
sum-to-exact-matching step is not proved, and those multiplicities are not tied to
physical field counters. The [machine targets](Airbender/Review/Compiler/MachineTargets.lean)
take public text and a public program setup. Native adapters cover all 14 CPU
profiles in both cache modes. They derive source constraints and public decoder
membership from physical row certificates and exact matching.
The [native acceptance adapter](Airbender/Proofs/GKRProtocol/NativeMachineAcceptance.lean)
closes the CPU and decoder target premises.
Earlier [captured-program boundaries](Airbender/Proofs/Compatibility/Compiler/Program.lean)
retain their structural decoder equality and image contracts for compatibility.
Explicit Airbender-platform wrappers retain their device configuration.
Generic wrappers remain polymorphic in the platform. See the
[execution premise table](Airbender/Review/Compiler/README.md#execution-premises).

[Verification status](VERIFICATION_STATUS.md#validation-evidence) records completed
source/runtime, native-capture and focused replay evidence, and the uncompleted
whole-environment/transitive assurance gates. Direct axiom reports can omit
imported constructor-type dependencies and do not replace the environment audit.

## Arithmetic extension and logical arguments

The [arithmetic claims](Airbender/Proofs/Compatibility/Compiler/Theorems.lean) distinguish
backward preservation from witness extension. Preservation derives every original
source arithmetic assertion from the whole captured native base-field relation.
Extension constructs an assignment satisfying only a certificate-selected native
arithmetic gate slice. The certificate is untrusted and Lean checks its selected
identities; it does not prove the slice covers every source-related emitted gate
or construct a witness for the complete GKR graph.

Standalone wiring, lookup-output and RAM-product reductions do not by themselves
turn balanced sampled sums/products into exact membership or token permutations.
Those logical-argument and public-boundary conditions remain visible in the
[compiler contracts](Airbender/Review/Compiler/README.md#execution-premises).
Universal correctness of the Rust compiler, cryptographic enforcement and
whole-system completeness remain outside these captured-instance results.

## Evidence and reproduction

Use [verification status](VERIFICATION_STATUS.md#validation-evidence) for evidence,
measurements and pending gates, and [reproduction](README.md#reproduce) for the
native setup/compiler, source/runtime, environment-audit and replay commands.
The source-bound window-semantics validator and full lookup-premise generator
run in CI and the complete frontend. Native setup and compiler build directories
are separate, including restored warm caches, so compiler-only dep-info cannot
contaminate setup receipts.

The [historical compiler record](GKR_COMPILER_VERIFICATION_HISTORY.md) preserves
dated checkpoints. It does not establish a current-head pass.
