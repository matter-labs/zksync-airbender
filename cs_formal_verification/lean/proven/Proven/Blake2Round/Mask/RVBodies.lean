module
public import Proven.Blake2Round.Mask.RVNext
public import Proven.Deleg.BlakeCall

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The prepared RV vector for the native first-mask-bit rule. -/
def maskedPrepared (control : RV.Word) (h : Vector RV.Word 8) (e : Vector RV.Word 16) : Vector RV.Word 16 :=
  if RV.Delegation.roundMaskBit control 0 then RV.bV0 (control.getLsbD 18) h e else e

/-- The selected RV message block before the mask schedule. -/
def maskedMessage (control : RV.Word) (h : Vector RV.Word 8) (m : Vector RV.Word 16) : Vector RV.Word 16 :=
  RV.bMsg (control.getLsbD 17) (control.getLsbD 18) h m

/-- The complete RV working vector for a native mask. -/
def maskedMixed (control : RV.Word) (h : Vector RV.Word 8) (e m : Vector RV.Word 16) : Vector RV.Word 16 :=
  Spec.round (RV.Delegation.maskedRoundMessage control (maskedMessage control h m)) id (maskedPrepared control h e)

/-- The pure native mask effect on already-read blocks. -/
def maskedBody (state control : RV.Word) (h : Vector RV.Word 8) (e m : Vector RV.Word 16) : RV.Effect :=
  let v := maskedMixed control h e m
  ⟨RV.writesAt state (if RV.Delegation.maskedRoundFinal control then
      RV.blakeFinal (RV.bH0 (control.getLsbD 18) h) v else h) ++ RV.writesAt (state + 32) v,
    12, nextBits control⟩

/-- The pure valid-schedule vector on already-read blocks. -/
def scheduledMixed (control : RV.Word) (r : Nat) (h : Vector RV.Word 8) (e m : Vector RV.Word 16) : Vector RV.Word 16 :=
  Spec.round (maskedMessage control h m) (Spec.SIGMA ⟨r % 10, Nat.mod_lt _ (by decide)⟩)
    (if r = 0 then RV.bV0 (control.getLsbD 18) h e else e)

/-- The pure valid-schedule effect on already-read blocks. -/
def scheduledBody (state control : RV.Word) (r : Nat) (h : Vector RV.Word 8) (e m : Vector RV.Word 16) : RV.Effect :=
  let v := scheduledMixed control r h e m
  ⟨RV.writesAt state (if r + 1 = (if control.getLsbD 16 then 7 else 10) then
      RV.blakeFinal (RV.bH0 (control.getLsbD 18) h) v else h) ++ RV.writesAt (state + 32) v,
    12, nextBits control⟩

/-- Reading the three source blocks gives the factored native RV body. -/
theorem masked_reads (state message control : RV.Word) (mem : RV.Word → BitVec 8) :
    RV.Delegation.blakeRoundMasked state message control mem =
      maskedBody state control (RV.readWords mem state 8) (RV.readWords mem (state + 32) 16)
        (RV.readWords mem message 16) := by
  cases first : RV.Delegation.roundMaskBit control 0
  all_goals simp only [RV.Delegation.blakeRoundMasked, maskedBody, maskedMixed, maskedPrepared,
    maskedMessage, first, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

end Airbender.Blake2Round.Mask.Proofs
