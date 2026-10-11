import Airbender.Proofs.Delegation.SharedSpans
import Airbender.Proofs.Delegation.SharedOperations
import Airbender.Proofs.Delegation.SharedMemory
import Airbender.Proofs.Delegation.RequestEffects
import Airbender.Proofs.Delegation.RequestTrace
import Airbender.Proofs.Delegation.Decoder
import Airbender.Review.Delegation.Theorems

namespace Airbender.Delegation.Caller

/-- Public instruction bytes and modeled decoder membership identify the
    request's family. Imported equations then prove its virtual CSR read/write
    tokens, real x0 addresses and state-preserving Sail register effects. Native
    source-value equality and fulfillment matching are separate; this theorem
    does not assume a selected opcode, expected request or expected output. -/
theorem soundness [Fact p.Prime] (hp : 65536 < p)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : programImage before addresses = some program)
    (member : (decoderTable program).Contains #[] (nativeQuery w)) :
    Binding w before program :=
  Proofs.caller_binding hp constraints image member

/-- Imported caller PCs match the original Sail preparation/retirement path.
    Public decoding supplies the initial word; imported range queries supply
    the final bounds. The inverse condition names the serialized field constant.
    No per-row PC range or expected next-PC premise is needed. -/
theorem pc_soundness [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : programImage before addresses = some program)
    (member : (decoderTable program).Contains #[] (nativeQuery w)) :
    PCBinding w before program :=
  Proofs.pc_binding hp inverse constraints image member

/-- Bind public caller instructions to actual worker rows through the native
    request permutation. Initialized machine clocks prove invocation bounds
    and write-offset room for the entire worker pool. Zero-clock workers remain
    an explicit gap; architectural caller/worker memory composition is separate. -/
theorem requests_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} (accepted : RequestAccepted data)
    (inputs : RequestInputs data before addresses) : RequestBinding data before :=
  Proofs.request_binding hp clockInverse pcInverse accepted inputs

/-- Connect caller requests to the worker pool's actual Sail memory effects.
    Public initialization and logical native permutations supply the inputs;
    invocation bounds and write-offset room come from the machine state path.
    This does not claim whole-machine execution or close zero-clock fulfillment. -/
theorem request_memory_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : RequestAccepted data) (inputs : RequestMemoryInputs data before addresses cells) :
    RequestExecution data before cells :=
  Proofs.request_memory_execution hp clockInverse pcInverse accepted inputs

/-- Decoded callers are linked to actual initialized workers whose native port
    effects match the named bigint/Clean hash references. All worker bounds and
    timestamp room are derived. Public initialization, modeled tables and the
    visible extended-round ABI remain; mixed architectural memory and span
    segmentation are separate. BabyBear is explicit because bigint's current
    multiplication proof uses that artifact's coefficients. -/
theorem operation_soundness
    {data : RequestTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {cells : List Trace.Cell} (accepted : RequestAccepted data)
    (inputs : RequestOperationInputs data before addresses cells) :
    RequestOperationEffects data before cells :=
  Proofs.request_operation_effects accepted inputs

/-- Caller and worker GPR/RAM transfers execute in one initialized Sail history.
    The virtual CSR port stays in its own request permutation. Shared matching
    proves the caller's canonical x0 source and every worker address bound;
    no worker-only memory permutation or expected read is assumed. This claim
    admits caller machine rows only; operation/span and mixed ISA composition
    remain separate obligations. -/
theorem shared_memory_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedMemoryInputs data before addresses cells) :
    SharedMemoryEffects data before cells :=
  Proofs.shared_memory_execution hp clockInverse pcInverse accepted inputs

/-- Caller and worker accesses share initialization, memory matching and actual
    Sail transfers. The same history derives all operand/pointer/result bounds
    and connects native port values to the four existing operation references.
    Only modeled tables and the extended-round ABI are added to public inputs;
    span ABI and standard/custom machine composition remain open. -/
theorem shared_operation_soundness
    {data : RequestTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedOperationInputs data before addresses cells) :
    SharedOperationEffects data before cells :=
  Proofs.shared_operation_effects accepted inputs

/-- A complete existing hash span reaches its reference result in the same
    state that realizes every shared terminal token. Worker memory matching,
    initialization, clock room and control-cell coverage are derived from the
    caller/worker pool. Only public mode/control and the existing span-size ABI
    boundary remain; mixed ISA composition and zero-clock exclusion stay open. -/
theorem shared_span_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : HashSpan}
    (accepted : SharedMemoryAccepted data) (inputs : SharedSpanInputs data before addresses cells span) :
    SharedSpanEffects data before cells span :=
  Proofs.shared_span_effects hp inverse accepted inputs

end Airbender.Delegation.Caller
