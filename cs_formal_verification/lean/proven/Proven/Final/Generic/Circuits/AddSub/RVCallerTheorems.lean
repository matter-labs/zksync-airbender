module
public import Human.Circuits.AddSub.RVCallerTheorems

/-! The generic-prime forms of the claims of `human/Human/Circuits/AddSub/RVCallerTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The proven proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.Delegation.Caller
def RVPcSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 196608 < p) (_inverse : (-30720 : ZMod p) * 65536 = 1) {before : RV.State} {addresses : List (BitVec 32)} {program : List RVProgramEntry} {w : Nat → ZMod p} (_constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints) (_image : rvProgramImage before addresses = some program) (_member : (rvDecoderTable program).Contains #[] (nativeQuery w)),
    RVPCBinding w before program

end Airbender.Delegation.Caller
