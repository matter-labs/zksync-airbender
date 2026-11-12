module
public import Human.Trace.Families.JumpBranchSlt.RVTheorems

/-! The generic-prime forms of the claims of `human/Human/Trace/Families/JumpBranchSlt/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The slop proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.JumpBranchSlt
open Trace
def RVTraceSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 4194304 ≤ p) (_inverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p} {initial : RV.State} {cells : List Trace.Cell} {program : List RVProgramEntry} (_inputs : RVExecutionInputs trace initial cells program) (_accepted : Trace.Accepted trace) (_decoded : RVDecoded trace program),
    Trace.RVRealizes trace initial cells

end Airbender.JumpBranchSlt
