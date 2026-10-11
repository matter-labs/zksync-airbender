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
    RequestExecution data before cells := by
  have requests := requests_soundness hp clockInverse pcInverse accepted inputs.publicProgram
  have publicState : MemoryInputs data.workers before cells :=
    ⟨inputs.initialization, inputs.distinct, requests.clockRoom⟩
  exact ⟨requests, Delegation.memory_soundness hp accepted.workers publicState,
    Delegation.native_memory_execution hp accepted.workers publicState inputs.aligned⟩

end Airbender.Delegation.Caller
