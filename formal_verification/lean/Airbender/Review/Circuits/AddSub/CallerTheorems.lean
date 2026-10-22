import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Delegation.Decoder
import Airbender.Proofs.Delegation.CallerPC

/-!
A decoded ADD/SUB caller row issues a virtual CSR request and retires its PC
under the original Sail caller effects. These results bind the request family,
x0 register effects and PC transition. Fulfilled worker effects and complete
protocol spans are connected by the
[trace entrypoints](../../Trace/Delegation/CallerTheorems.lean).
-/

namespace Airbender.Delegation.Caller

/-- Public instruction bytes and modeled decoder membership identify the
    request's family. Imported equations then prove its virtual CSR read/write
    tokens, real x0 addresses and state-preserving Sail register effects. Native
    source-value equality and fulfillment matching are separate; this theorem
    does not assume a selected opcode, expected request or expected output. -/
theorem soundness [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
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
theorem pc_soundness [Fact p.Prime] (hp : FieldCapacity.NoWrap p 196608)
    (inverse : SerializedInverse.Limb16 p)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : programImage before addresses = some program)
    (member : (decoderTable program).Contains #[] (nativeQuery w)) :
    PCBinding w before program :=
  Proofs.pc_binding hp inverse constraints image member

end Airbender.Delegation.Caller
