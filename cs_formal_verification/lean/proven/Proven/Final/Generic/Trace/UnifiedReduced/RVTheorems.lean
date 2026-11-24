module
public import Human.Trace.UnifiedReduced.RVTheorems

/-! The generic-prime forms of the claims of `human/Human/Trace/UnifiedReduced/RVTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The proven proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.UnifiedReduced
def RVExecutionSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 4194304 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_byteInverse : 256 * (-7864320 : ZMod p) = 1) {trace : Trace.UnifiedTrace p} {initial : RV.State} {cells : List Trace.Cell} {program : List RVProgramEntry} {inits : List (InitsTeardowns.Witness p InitsTeardowns.unifiedLayout)} (_inputs : RVExecutionInputs trace initial cells program inits) (_accepted : Trace.Accepted trace) (_decoded : RVDecoded trace program),
    Trace.RVRealizes trace initial cells

end Airbender.UnifiedReduced
