import Human.Circuits.AddSub.RVCallerTheorems
import Slop.Delegation.RVCallerDecoder

namespace Airbender.Delegation.Caller

/-- RV sibling of `soundness`: public ROM bytes, `RV.decode` and modeled decoder membership identify the request's
    family and its delegation call; imported equations prove its CSR tokens, x0 addresses and RV x0 effects. -/
theorem rv_soundness [Fact p.Prime] (hp : 65536 < p)
    {before : RV.State} {addresses : List (BitVec 32)}
    {program : List RVProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : rvProgramImage before addresses = some program)
    (member : (rvDecoderTable program).Contains #[] (nativeQuery w)) :
    RVBinding w before program :=
  Proofs.rv_caller_binding hp constraints image member

/-- RV sibling of `pc_soundness`: imported caller PCs match the RV retirement path. -/
theorem rv_pc_soundness [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {before : RV.State} {addresses : List (BitVec 32)}
    {program : List RVProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : rvProgramImage before addresses = some program)
    (member : (rvDecoderTable program).Contains #[] (nativeQuery w)) :
    RVPCBinding w before program :=
  Proofs.rv_pc_binding hp inverse constraints image member

end Airbender.Delegation.Caller
