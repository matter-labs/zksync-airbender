import Airbender.Review.UnifiedReduced.Model
import Airbender.Proofs.UnifiedReduced
import Airbender.Proofs.AddSub

namespace Airbender.UnifiedReduced.Proofs
open Airbender.Reference.RiscV
open Airbender.Arithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

private theorem other_standard_flags {p : Nat} [Fact p.Prime] (hp : 18 < p)
    {setup : Table (ZMod p) (fields 10)} {input : Sail.Input} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (dc : DecoderContract input w) :
    ∀ i : Fin 18, 3 ≤ i.val → w Variables.dispatchColumns[i] = 0 := by
  have small : (standardSelector input).val < 3 := by
    unfold standardSelector
    split
    · decide
    · cases input.row.opcode <;> decide
  intro i outside
  apply dispatch_exclusive hp h dc.active (standardSelector input) dc.selected i
  intro same
  have equal := congrArg Fin.val same
  omega

private theorem standard_selectors {p : Nat} [Fact p.Prime] (hp : 18 < p)
    {setup : Table (ZMod p) (fields 10)} {input : Sail.Input} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (dc : DecoderContract input w) (nonzero : input.rd ≠ Sail.zeroRegister) :
    w 11 = (if input.row.opcode = .sub ∨ input.row.opcode = .auipc then 0 else 1) ∧
    w 12 = (if input.row.opcode = .sub then 1 else 0) ∧
    w 13 = (if input.row.opcode = .auipc then 1 else 0) := by
  have selected := dc.selected
  have other := dispatch_exclusive hp h dc.active (standardSelector input) selected
  cases hop : input.row.opcode <;>
    simp only [standardSelector, nonzero, if_false, hop] at selected other ⊢
  all_goals repeat' apply And.intro
  all_goals first
    | exact selected
    | exact other 0 (by decide)
    | exact other 1 (by decide)
    | exact other 2 (by decide)

private theorem selected_equations {p : Nat} [Fact p.Prime] (hp : 18 < p)
    {setup : Table (ZMod p) (fields 10)} {input : Sail.Input} {output : Sail.Output}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (dc : DecoderContract input w) (nonzero : input.rd ≠ Sail.zeroRegister)
    (wm : WordMapping input output w) :
    match input.row.opcode with
    | .sub =>
      (output.destination.lo : ZMod p) + input.row.right.lo = input.row.left.lo + 65536 * (w 53).val ∧
      ((w 53).val : ZMod p) + output.destination.hi + input.row.right.hi = input.row.left.hi + 65536 * (w 52).val
    | .auipc =>
      (input.row.pc.lo : ZMod p) + input.row.immediate.lo = output.destination.lo + 65536 * (w 53).val ∧
      ((w 53).val : ZMod p) + input.row.pc.hi + input.row.immediate.hi = output.destination.hi + 65536 * (w 52).val
    | _ =>
      (input.row.left.lo : ZMod p) + input.row.right.lo + input.row.immediate.lo = output.destination.lo + 65536 * (w 53).val ∧
      ((w 53).val : ZMod p) + input.row.left.hi + input.row.right.hi + input.row.immediate.hi = output.destination.hi + 65536 * (w 52).val := by
  have outLo : w 50 = (output.destination.lo : ZMod p) := by
    rw [wm.outputLo]; exact (ZMod.natCast_zmod_val _).symm
  have outHi : w 51 = (output.destination.hi : ZMod p) := by
    rw [wm.outputHi]; exact (ZMod.natCast_zmod_val _).symm
  have lo := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  have other := other_standard_flags hp h dc
  have s14 : w 14 = 0 := other 3 (by decide)
  have s15 : w 15 = 0 := other 4 (by decide)
  have s16 : w 16 = 0 := other 5 (by decide)
  have s17 : w 17 = 0 := other 6 (by decide)
  have s20 : w 20 = 0 := other 9 (by decide)
  have selectors := standard_selectors hp h dc nonzero
  cases hop : input.row.opcode <;> simp only [hop] at selectors ⊢
  all_goals
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
      selectors.1, selectors.2.1, selectors.2.2, s14, s15, s16, s17, s20, wm.leftLo, wm.leftHi, wm.rightLo,
      wm.rightHi, wm.immediateLo, wm.immediateHi, wm.pcLo, wm.pcHi, outLo, outHi] at lo hi
    constructor <;> simp only [ZMod.natCast_zmod_val]
    all_goals solve
      | (apply sub_eq_zero.mp; convert lo using 1; ring)
      | (apply sub_eq_zero.mp; convert hi using 1; ring)

private theorem output_bounds {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {input : Sail.Input} {output : Sail.Output}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mapping : WordMapping input output w) : output.destination.Bounded := by
  have lo := Verification.range16_bound (Verification.lookup_of_holds h ⟨2, by rw [lookup_count]; decide⟩)
  have hi := Verification.range16_bound (Verification.lookup_of_holds h ⟨3, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at lo hi
  exact ⟨mapping.outputLo ▸ lo, mapping.outputHi ▸ hi⟩

/-- Standard instructions reuse the standalone limb calculation and native Sail
    execution/retirement proofs; only the imported placement and gates differ. -/
theorem standard_soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (setup : Table (ZMod p) (fields 10)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions Sail.spec := by
  rintro input output w ⟨assumptions, constraints, mapping⟩
  have other := other_standard_flags (by omega) constraints assumptions.decoder
  have outside : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 :=
    ⟨other 10 (by decide), other 11 (by decide), other 12 (by decide), other 13 (by decide)⟩
  have pc := pc_successor (by omega) constraints assumptions.decoder.active outside
    ⟨mapping.pcLo, mapping.pcHi, mapping.finalPCLo, mapping.finalPCHi⟩ assumptions.initialPCBounds
  apply Sail.step_of_destination assumptions.registers pc.2.2
  intro state contract
  by_cases hz : input.rd = Sail.zeroRegister
  · exact Sail.spec_zero_write contract hz
  · apply Sail.spec_of_result contract hz
    exact AddSub.Proofs.result_of_limbs (input := input) (output := output) hp hz assumptions.decoder.preprocessing
      (assumptions.ranges hz) assumptions.initialPCBounds (output_bounds constraints mapping)
      (boolean_val (local_flags constraints 21)) (boolean_val (local_flags constraints 20))
      (selected_equations (by omega) constraints assumptions.decoder hz mapping)

end Airbender.UnifiedReduced.Proofs
