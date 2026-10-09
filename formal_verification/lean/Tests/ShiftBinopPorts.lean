import Airbender.Proofs.ShiftBinop.Ports
import Tests.ShiftBinopTimestamp

namespace Tests.ShiftBinopPorts
open Airbender
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- SLL x1,x0,x0. The unused high rs2 bytes cancel in Rust's field packing;
    they are deliberately not both canonical byte values. -/
private def row (i : Nat) : ZMod babyBearModulus :=
  if i = 11 ∨ i = 27 ∨ i = 59 ∨ i = 65 ∨ i = 68 ∨ i = 77 ∨ i = 86 then 1
  else if i = 12 then 0
  else if i = 28 then 7864320
  else if i = 10 then 1
  else if i = 55 then 8
  else if i = 64 ∨ i = 73 ∨ i = 82 ∨ i = 91 then 9
  else if i = 74 then 2
  else if i = 83 then 3
  else Tests.ShiftBinopTimestamp.assignment false i

theorem constraints :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      Airbender.ShiftBinop.importedConstraints := by
  simp [Airbender.ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, row, Tests.ShiftBinopTimestamp.assignment,
    Tests.ShiftBinop.row]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 8] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨196865, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨196865, by decide⟩ =
           (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 8] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[0, 0, 0, 1, 0, 0, 0, 0, 0, 9] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨262402, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨262402, by decide⟩ =
           (#v[0, 0, 0, 1, 0, 0, 0, 0, 0, 9] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[1, 0, 0, 1, 0, 0, 0, 0, 0, 9] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨327938, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨327938, by decide⟩ =
           (#v[1, 0, 0, 1, 0, 0, 0, 0, 0, 9] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[2, 0, 0, 1, 0, 0, 0, 0, 0, 9] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨393474, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨393474, by decide⟩ =
           (#v[2, 0, 0, 1, 0, 0, 0, 0, 0, 9] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[3, 0, 0, 1, 0, 0, 0, 0, 0, 9] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨459010, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨459010, by decide⟩ =
           (#v[3, 0, 0, 1, 0, 0, 0, 0, 0, 9] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)

/-- The amount is derived from the packed x0 read despite an unbounded unused
    high byte. This is an accepted representation, not a soundness counterexample. -/
theorem unused_high_bytes :
    (row 28).val = 7864320 ∧
      Airbender.ShiftBinop.importedConstraintsMemoryPorts[1].readCode row = 0 ∧
      row 25 = ((Trace.Proofs.memoryWord
        (Airbender.ShiftBinop.importedConstraintsMemoryPorts[1].readCode row)).extractLsb' 0 8).toNat := by
  refine ⟨by decide, by decide, ?_⟩
  exact Airbender.ShiftBinop.Proofs.shift_right_low_byte (by decide) constraints ⟨by decide, by decide⟩

end Tests.ShiftBinopPorts
