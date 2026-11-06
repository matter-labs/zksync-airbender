import Airbender.Proofs.ReducedMachine.NativeShiftNaturalViews
import Airbender.Proofs.ReducedMachine.NativeShiftBoundsLeft
import Airbender.Proofs.ReducedMachine.NativeShiftBoundsArithmetic
import Airbender.Proofs.ReducedMachine.NativeShiftContributions
import Airbender.Proofs.ReducedMachine.NativeShiftFill
import Airbender.Proofs.ReducedMachine.NativeShiftWrite

namespace Airbender.ReducedMachine.NativeShiftBoundedProofs
open Native Verification NativeShiftNaturalProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem sum3 (a b c : ZMod mersenne31Modulus)
    (ha : a.val < 65536) (hb : b.val < 65536) (hc : c.val < 65536) :
    (a + b + c).val = a.val + b.val + c.val := by
  have small : a.val + b.val + c.val < mersenne31Modulus := by change _ < 2147483647; omega
  have field : ((a.val + b.val + c.val : Nat) : ZMod mersenne31Modulus) = a + b + c := by
    simp only [Nat.cast_add,ZMod.natCast_zmod_val]
  have natural := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt small] at natural
  exact natural.symm
private theorem sum2 (a b : ZMod mersenne31Modulus) (ha : a.val < 65536) (hb : b.val < 65536) :
    (a + b).val = a.val + b.val := by
  simpa only [add_zero,ZMod.val_zero] using sum3 a b 0 ha hb (by decide)

/-- Internal source-bound lifting only; public initialized induction must supply the source bound. -/
theorem candidate_values {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus))
    (source : (source1 w)[0].val < 65536 ∧ (source1 w)[1].val < 65536) :
    (w 116).val = assembledLow mode (source1 w)[0].val (source1 w)[1].val (shiftAmount w).val ∧
      (w 117).val = assembledHigh mode (source1 w)[0].val (source1 w)[1].val (shiftAmount w).val := by
  have amount := (NativeShiftRoutingProofs.amount holds mode useRegister mask).2.2.1
  have decoded (limb : Fin 2) :
      (shiftContribution w limb)[0].val = (outputs mode (source1 w)[limb].val (shiftAmount w).val)[0] ∧
      (shiftContribution w limb)[1].val = (outputs mode (source1 w)[limb].val (shiftAmount w).val)[1] := by
    have bound : (source1 w)[limb].val < 65536 := by fin_cases limb; exact source.1; exact source.2
    have value := NativeShiftContributionProofs.values holds mode useRegister mask limb
    rw [canonical_key mode _ _ bound amount,packed_outputs mode _ _ bound amount] at value
    exact ⟨value.2.1,value.2.2.1⟩
  have low := decoded ⟨0,by decide⟩
  have high := decoded ⟨1,by decide⟩
  change (shiftLowParts w)[0].val = _ ∧ (shiftLowParts w)[1].val = _ at low
  change (shiftHighParts w)[0].val = _ ∧ (shiftHighParts w)[1].val = _ at high
  have lb := (NativeShiftContributionProofs.values holds mode useRegister mask ⟨0,by decide⟩).2.2.2
  have hb := (NativeShiftContributionProofs.values holds mode useRegister mask ⟨1,by decide⟩).2.2.2
  have filler := NativeShiftFillProofs.result holds mode useRegister mask
  have fvalue := filler.1
  change (shiftSignFill w)[0].val + 65536 * (shiftSignFill w)[1].val =
    mode.filler (source1 w)[1].val (shiftAmount w).val at fvalue
  have fl : (shiftSignFill w)[0].val = mode.filler (source1 w)[1].val (shiftAmount w).val % 65536 := by omega
  have fh : (shiftSignFill w)[1].val = mode.filler (source1 w)[1].val (shiftAmount w).val / 65536 := by omega
  have candidate := NativeShiftWriteProofs.candidate holds mode useRegister mask
  have first := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) candidate
  have second := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) candidate
  cases mode
  · constructor
    · change w 116 = (shiftLowParts w)[0] + (shiftSignFill w)[0] at first
      rw [first,sum2 (shiftLowParts w)[0] (shiftSignFill w)[0] lb.1 filler.2.1]
      rw [low.1,fl]
      simp [assembledLow,output0,ShiftMode.filler]
    · change w 117 = (shiftHighParts w)[0] + (shiftLowParts w)[1] + (shiftSignFill w)[1] at second
      rw [second,sum3 (shiftHighParts w)[0] (shiftLowParts w)[1] (shiftSignFill w)[1] hb.1 lb.2 filler.2.2]
      rw [high.1,low.2,fh]
      simp [assembledHigh,output0,output1,ShiftMode.filler]
  · constructor
    · change w 116 = (shiftLowParts w)[0] + (shiftHighParts w)[1] + (shiftSignFill w)[0] at first
      rw [first,sum3 (shiftLowParts w)[0] (shiftHighParts w)[1] (shiftSignFill w)[0] lb.1 hb.2 filler.2.1]
      rw [low.1,high.2,fl]
      simp [assembledLow,output0,output1,ShiftMode.filler]
    · change w 117 = (shiftHighParts w)[0] + (shiftSignFill w)[1] at second
      rw [second,sum2 (shiftHighParts w)[0] (shiftSignFill w)[1] hb.1 filler.2.2]
      rw [high.1,fh]
      simp [assembledHigh,output0,ShiftMode.filler]
  · constructor
    · change w 116 = (shiftLowParts w)[0] + (shiftHighParts w)[1] + (shiftSignFill w)[0] at first
      rw [first,sum3 (shiftLowParts w)[0] (shiftHighParts w)[1] (shiftSignFill w)[0] lb.1 hb.2 filler.2.1]
      rw [low.1,high.2,fl]
      simp [assembledLow,output0,output1,ShiftMode.filler]
    · change w 117 = (shiftHighParts w)[0] + (shiftSignFill w)[1] at second
      rw [second,sum2 (shiftHighParts w)[0] (shiftSignFill w)[1] hb.1 filler.2.2]
      rw [high.1,fh]
      simp [assembledHigh,output0,ShiftMode.filler]

/-- Native candidate limbs are bounded once earlier initialized reads are bounded. -/
theorem candidate_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus))
    (source : (source1 w)[0].val < 65536 ∧ (source1 w)[1].val < 65536) :
    (w 116).val < 65536 ∧ (w 117).val < 65536 := by
  have amount := (NativeShiftRoutingProofs.amount holds mode useRegister mask).2.2.1
  have values := candidate_values holds mode useRegister mask source
  have bounds : assembledLow mode (source1 w)[0].val (source1 w)[1].val (shiftAmount w).val < 65536 ∧
      assembledHigh mode (source1 w)[0].val (source1 w)[1].val (shiftAmount w).val < 65536 := by
    cases mode
    · exact left_bounds _ _ ⟨_,amount⟩ source.1 source.2
    · exact right_bounds _ _ ⟨_,amount⟩ source.1 source.2
    · exact arithmetic_bounds _ _ ⟨_,amount⟩ source.1 source.2
  exact ⟨values.1 ▸ bounds.1,values.2 ▸ bounds.2⟩

end Airbender.ReducedMachine.NativeShiftBoundedProofs
