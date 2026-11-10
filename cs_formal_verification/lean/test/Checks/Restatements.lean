import Slop.Field.BabyBearInstance
import Slop.Deleg.BlakeRun
import Slop.Final.Generic.Circuits.AddSub.RVCallerTheorems
import Slop.Final.Generic.Circuits.AddSub.RVTheorems
import Slop.Final.Generic.Circuits.Bigint.RVTheorems
import Slop.Final.Generic.Circuits.Blake2G.Theorems
import Slop.Final.Generic.Circuits.JumpBranchSlt.RVTheorems
import Slop.Final.Generic.Circuits.MulDiv.RVTheorems
import Slop.Final.Generic.Circuits.ShiftBinop.RVTheorems
import Slop.Final.Generic.Circuits.SubwordMemory.RVTheorems
import Slop.Final.Generic.Circuits.WordMemory.RVTheorems
import Slop.Final.Generic.Trace.Delegation.RVCallerTheorems
import Slop.Final.Generic.Trace.Delegation.RVTheorems
import Slop.Final.Generic.Trace.Families.JumpBranchSlt.RVTheorems
import Slop.Final.Generic.Trace.Families.MulDiv.RVTheorems
import Slop.Final.Generic.Trace.Families.ShiftBinop.RVTheorems
import Slop.Final.Generic.Trace.Families.SubwordMemory.RVTheorems
import Slop.Final.Generic.Trace.UnifiedReduced.RVCallerTheorems
import Slop.Final.Generic.Trace.UnifiedReduced.RVTheorems
import Slop.Final.Generic.Trace.Workers.Blake2G.RVTheorems
import Slop.Final.Generic.Trace.Workers.Blake2Round.RVTheorems
import Slop.Final.Generic.Trace.Workers.Keccak.RVTheorems
import Slop.Final.Generic.Trace.Workers.KeccakSplit.RVTheorems
import Human.Circuits.AddSub.RVCallerTheorems
import Human.Circuits.AddSub.RVTheorems
import Human.Circuits.Bigint.RVTheorems
import Human.Circuits.Blake2G.Theorems
import Human.Circuits.JumpBranchSlt.RVTheorems
import Human.Circuits.MulDiv.RVTheorems
import Human.Circuits.ShiftBinop.RVTheorems
import Human.Circuits.SubwordMemory.RVTheorems
import Human.Circuits.WordMemory.RVTheorems
import Human.Trace.Delegation.RVCallerTheorems
import Human.Trace.Delegation.RVTheorems
import Human.Trace.Families.JumpBranchSlt.RVTheorems
import Human.Trace.Families.MulDiv.RVTheorems
import Human.Trace.Families.ShiftBinop.RVTheorems
import Human.Trace.Families.SubwordMemory.RVTheorems
import Human.Trace.UnifiedReduced.RVCallerTheorems
import Human.Trace.UnifiedReduced.RVTheorems
import Human.Trace.Workers.Blake2G.RVTheorems
import Human.Trace.Workers.Blake2Round.RVTheorems
import Human.Trace.Workers.Keccak.RVTheorems
import Human.Trace.Workers.KeccakSplit.RVTheorems

/-! Restatement check (P4): every claim restated in human/ is equivalent to its previous text.

D1: each claim that was stated for every prime `p` with an inverse premise (which forces `p = babyBearModulus`) is
now stated at BabyBear; `<Claim>Generic` (slop/Slop/Final/Generic/) is the previous text verbatim. The nine
`BabyBear…` twins were the new text character for character (checked below by `Iff.rfl`). -/

example : Airbender.Delegation.Caller.RVPcSoundnessClaimGeneric ↔ Airbender.Delegation.Caller.RVPcSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.AddSub.RVSoundnessClaimGeneric ↔ Airbender.AddSub.RVSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Bigint.Memory.RVAddressesSoundnessClaimGeneric ↔ Airbender.Bigint.Memory.RVAddressesSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Blake2G.SoundnessClaimGeneric ↔ Airbender.Blake2G.SoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.JumpBranchSlt.Comparison.RVSoundnessClaimGeneric ↔ Airbender.JumpBranchSlt.Comparison.RVSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.JumpBranchSlt.Branch.RVSoundnessClaimGeneric ↔ Airbender.JumpBranchSlt.Branch.RVSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.JumpBranchSlt.Jump.RVSoundnessClaimGeneric ↔ Airbender.JumpBranchSlt.Jump.RVSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.MulDiv.RVSoundnessClaimGeneric ↔ Airbender.MulDiv.RVSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.ShiftBinop.RVSoundnessClaimGeneric ↔ Airbender.ShiftBinop.RVSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.SubwordMemory.RVSoundnessClaimGeneric ↔ Airbender.SubwordMemory.RVSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.WordMemory.RVSoundnessClaimGeneric ↔ Airbender.WordMemory.RVSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Delegation.Caller.RVRequestsSoundnessClaimGeneric ↔ Airbender.Delegation.Caller.RVRequestsSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Delegation.Caller.RVRequestMemorySoundnessClaimGeneric ↔ Airbender.Delegation.Caller.RVRequestMemorySoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Delegation.Caller.RVSharedMemorySoundnessClaimGeneric ↔ Airbender.Delegation.Caller.RVSharedMemorySoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Delegation.Caller.RVSharedSpanSoundnessClaimGeneric ↔ Airbender.Delegation.Caller.RVSharedSpanSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Delegation.Caller.RVWorkerScheduleSoundnessClaimGeneric ↔ Airbender.Delegation.Caller.RVWorkerScheduleSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Delegation.Caller.RVRequestWindowSoundnessClaimGeneric ↔ Airbender.Delegation.Caller.RVRequestWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Delegation.Caller.RVRequestHashWindowSoundnessClaimGeneric ↔ Airbender.Delegation.Caller.RVRequestHashWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _ _ _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Delegation.RVOperationMemorySoundnessClaimGeneric ↔ Airbender.Delegation.RVOperationMemorySoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.JumpBranchSlt.RVTraceSoundnessClaimGeneric ↔ Airbender.JumpBranchSlt.RVTraceSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.MulDiv.RVTraceSoundnessClaimGeneric ↔ Airbender.MulDiv.RVTraceSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.ShiftBinop.RVTraceSoundnessClaimGeneric ↔ Airbender.ShiftBinop.RVTraceSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.SubwordMemory.RVRamTraceSoundnessClaimGeneric ↔ Airbender.SubwordMemory.RVRamTraceSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVSharedSpanSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVSharedSpanSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVRequestWindowSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVRequestWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVRequestHashWindowSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVRequestHashWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _ _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVMixedWindowSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVMixedWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVJointHashWindowSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVJointHashWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVWindowProjectionSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVWindowProjectionSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVWindowScheduleSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVWindowScheduleSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVMixedWindowProjectionSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVMixedWindowProjectionSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVControlPreparationSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVControlPreparationSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVControlPreparationWindowSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVControlPreparationWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVMixedWindowChainSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVMixedWindowChainSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVMixedWindowSequenceSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVMixedWindowSequenceSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVPreparedHashWindowSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVPreparedHashWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVPreparedHashChainSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVPreparedHashChainSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVPreparedHashSequenceSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVPreparedHashSequenceSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVPreparedRoundRegionMasksSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVPreparedRoundRegionMasksSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVPreparedProtocolSequenceSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVPreparedProtocolSequenceSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVPreparedRoundMasksSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVPreparedRoundMasksSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVPreparedRoundWindowSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVPreparedRoundWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVProgramWindowScheduleSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVProgramWindowScheduleSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.Caller.RVProgramPreparedProtocolSequenceSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.Caller.RVProgramPreparedProtocolSequenceSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.UnifiedReduced.RVExecutionSoundnessClaimGeneric ↔ Airbender.UnifiedReduced.RVExecutionSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv _
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Blake2G.Native.RVWorkvectorSoundnessClaimGeneric ↔ Airbender.Blake2G.Native.RVWorkvectorSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Blake2G.Native.RVWorkvectorBoundarySoundnessClaimGeneric ↔ Airbender.Blake2G.Native.RVWorkvectorBoundarySoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Blake2G.Native.RVWindowSoundnessClaimGeneric ↔ Airbender.Blake2G.Native.RVWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Blake2G.Native.RVOperationExecutionClaimGeneric ↔ Airbender.Blake2G.Native.RVOperationExecutionClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Blake2Round.Native.RVOperationExecutionClaimGeneric ↔ Airbender.Blake2Round.Native.RVOperationExecutionClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Blake2Round.Native.RVCompressionSoundnessClaimGeneric ↔ Airbender.Blake2Round.Native.RVCompressionSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Blake2Round.Native.RVCompressionBoundarySoundnessClaimGeneric ↔ Airbender.Blake2Round.Native.RVCompressionBoundarySoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Blake2Round.Native.RVWindowSoundnessClaimGeneric ↔ Airbender.Blake2Round.Native.RVWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Keccak.Native.RVPermutationBoundarySoundnessClaimGeneric ↔ Airbender.Keccak.Native.RVPermutationBoundarySoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Keccak.Native.RVPermutationSoundnessClaimGeneric ↔ Airbender.Keccak.Native.RVPermutationSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Keccak.Native.RVOperationExecutionClaimGeneric ↔ Airbender.Keccak.Native.RVOperationExecutionClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Keccak.Native.RVWindowSoundnessClaimGeneric ↔ Airbender.Keccak.Native.RVWindowSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Keccak.Split.Native.RVOperationExecutionClaimGeneric ↔ Airbender.Keccak.Split.Native.RVOperationExecutionClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩
example : Airbender.Keccak.Split.Native.RVPermutationSoundnessClaimGeneric ↔ Airbender.Keccak.Split.Native.RVPermutationSoundnessClaim :=
  ⟨fun h => by babybear_instance h, fun h => by
    intro p _ inv
    have hb : ((Airbender.babyBearModulus : Nat) : ZMod p) = 0 := by
      rw [show Airbender.babyBearModulus = 2013265921 from rfl]; push_cast; linear_combination (-1 : ZMod p) * inv
    obtain rfl := Airbender.Field.eq_babyBear_of_cast_eq_zero hb
    exact @h⟩

namespace Airbender.AddSub
open Reference.RiscV Trace
-- The deleted `BabyBearRVSoundnessClaim`, verbatim.
example : (∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)) ↔ RVSoundnessClaim := Iff.rfl
end Airbender.AddSub

namespace Airbender.Blake2G
-- The deleted `BabyBearSoundnessClaim`, verbatim.
example : (∀ (control : Fin 512 → Vector Nat 7),
    (circuitModel (p := babyBearModulus) control).SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec) ↔ SoundnessClaim := Iff.rfl
end Airbender.Blake2G

namespace Airbender.JumpBranchSlt.Comparison
-- The deleted `BabyBearRVSoundnessClaim`, verbatim.
example : (∀ (trace : Trace.PooledTrace babyBearModulus) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)) ↔ RVSoundnessClaim := Iff.rfl
end Airbender.JumpBranchSlt.Comparison

namespace Airbender.JumpBranchSlt.Branch
-- The deleted `BabyBearRVSoundnessClaim`, verbatim.
example : (∀ (trace : Trace.PooledTrace babyBearModulus) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧ RV.Same s' (input.before.setPC output.pc.toBitVec)) ↔ RVSoundnessClaim := Iff.rfl
end Airbender.JumpBranchSlt.Branch

namespace Airbender.JumpBranchSlt.Jump
-- The deleted `BabyBearRVSoundnessClaim`, verbatim.
example : (∀ (trace : Trace.PooledTrace babyBearModulus) (initial : RV.State) (cells : List Trace.Cell) (program : List Trace.RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)) ↔ RVSoundnessClaim := Iff.rfl
end Airbender.JumpBranchSlt.Jump

namespace Airbender.MulDiv
open Trace
-- The deleted `BabyBearRVSoundnessClaim`, verbatim.
example : (∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)) ↔ RVSoundnessClaim := Iff.rfl
end Airbender.MulDiv

namespace Airbender.ShiftBinop
open Trace
-- The deleted `BabyBearRVSoundnessClaim`, verbatim.
example : (∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)) ↔ RVSoundnessClaim := Iff.rfl
end Airbender.ShiftBinop

namespace Airbender.SubwordMemory
open Trace
-- The deleted `BabyBearRVSoundnessClaim`, verbatim.
example : (∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      output.cell.toBitVec.toNat = (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' (if input.store then
            (input.before.store output.cell.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
          else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)) ↔ RVSoundnessClaim := Iff.rfl
end Airbender.SubwordMemory

namespace Airbender.WordMemory
open Trace
-- The deleted `BabyBearRVSoundnessClaim`, verbatim.
example : (∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    RVInterfaceAssumptions trace initial cells program →
    ∀ input output w, (rvCircuitModel trace initial cells program).relation input output w →
      output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec ∧
      ∃ s', RV.step input.before = some s' ∧
        RV.Same s' (if input.store then
            (input.before.store output.address.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
          else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)) ↔ RVSoundnessClaim := Iff.rfl
end Airbender.WordMemory

/-! C1: the merged constants have the deleted definitions' values. -/
example : RV.ROM_END = 4194304 := rfl          -- was `Trace.ROM.limit` and `Sail.Configuration.ROM_END`
example : RV.RAM_END = 0x100000000 := rfl      -- was `Sail.Configuration.RAM_END`
example : RV.BabyBearP = 0x78000001 := rfl     -- was its own literal; now `babyBearModulus`
example : RV.RINV = 0x38400000 := rfl          -- was its own literal; now `montgomeryInverse`

/-! C3: `Spec.compress` was spelled out with seven rounds; it is now `compressRounds 7`. -/
namespace Spec
open RV (Word)

/-- The previous `Spec.compress`, verbatim. -/
def oldCompress (h : Vector Word 8) (m : Vector Word 16) (t : Word) (last : Bool) : Vector Word 8 :=
  let v₀ : Vector Word 16 := #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV 0, IV 1, IV 2, IV 3,
    t ^^^ IV 4, IV 5, (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6, IV 7]
  let v := round m (SIGMA 6) <| round m (SIGMA 5) <| round m (SIGMA 4) <| round m (SIGMA 3) <|
    round m (SIGMA 2) <| round m (SIGMA 1) <| round m (SIGMA 0) v₀
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

theorem old_compress_eq (h : Vector Word 8) (m : Vector Word 16) (t : Word) (last : Bool) (e : Vector Word 16)
    (h12 : e[12] = t ^^^ IV 4) (h14 : e[14] = (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6) :
    oldCompress h m t last = RV.blakeFinal h (RV.blakeVs m (RV.blakeV0 h e) 7) := by
  have hv : RV.blakeV0 h e = #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV 0, IV 1, IV 2, IV 3,
      t ^^^ IV 4, IV 5, (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6, IV 7] := by
    rw [RV.blakeV0, h12, h14]
  rw [hv]
  rfl

example (h : Vector Word 8) (m : Vector Word 16) (t : Word) (last : Bool) :
    oldCompress h m t last = compress h m t last := by
  let e : Vector Word 16 := Vector.ofFn fun i =>
    if i.val = 12 then t ^^^ IV 4 else (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6
  have e12 : e[12] = t ^^^ IV 4 := by simp [e]
  have e14 : e[14] = (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6 := by simp [e]
  rw [old_compress_eq h m t last e e12 e14, RV.compress_eq h m t last e e12 e14]

end Spec
