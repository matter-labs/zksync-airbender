import Airbender.Proofs.Delegation.Decoder

namespace Airbender.Delegation.Caller

/-- Public instruction bytes and modeled decoder membership identify the
    request's family. Imported equations then prove its virtual CSR read/write
    tokens and zero destination. Fulfillment matching is separate; this theorem
    does not assume a selected opcode, expected request or expected output. -/
theorem soundness [Fact p.Prime] (hp : 65536 < p)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : programImage before addresses = some program)
    (member : (decoderTable program).Contains #[] (nativeQuery w)) :
    Binding w before program :=
  Proofs.caller_binding hp constraints image member

end Airbender.Delegation.Caller
