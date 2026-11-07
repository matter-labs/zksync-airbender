import Airbender.Proofs.Keccak.SplitThetaControllerRows
import Airbender.Proofs.Keccak.SplitControlBinding

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Active membership in the actual controller gives the original transition and exact column flags. -/
theorem theta_rho_controller_table_schedule (row : Vector (ZMod babyBearModulus) 9)
    (sound : (thetaRhoControl.table "Airbender.SplitThetaRhoControl").toRaw.Soundness #[] row)
    (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .thetaRho ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ column : Fin 5, row[3 + column.val] = if column.val = index.val % 5 then 1 else 0) := by
  change ∃ i : Fin thetaRhoControl.length,
    row = (thetaRhoControl.row i).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨i, rfl⟩ := sound
  have enabled : (thetaRhoControl.row i)[1] = 1 := by
    rcases theta_rho_controller_execute i with zero | one
    · simp [zero] at active
    · exact one
  obtain ⟨kind, before, after, flags⟩ := theta_rho_controller_schedule i enabled
  refine ⟨thetaRhoControllerIndex i, kind, ?_, ?_, ?_⟩
  · simpa only [Vector.getElem_map, Int.cast_natCast] using
      congrArg (fun value : Int => (value : ZMod babyBearModulus)) before
  · simpa only [Vector.getElem_map, Int.cast_natCast] using
      congrArg (fun value : Int => (value : ZMod babyBearModulus)) after
  · intro column
    have values := congrArg (fun value : Int => (value : ZMod babyBearModulus)) (flags column)
    by_cases selected : column.val = (thetaRhoControllerIndex i).val % 5
    · simpa only [Vector.getElem_map, if_pos selected, Int.cast_one] using values
    · simpa only [Vector.getElem_map, if_neg selected, Int.cast_zero] using values

/-- The retained complete generic extent supplies the exact original controller schedule. -/
theorem theta_rho_generic_controller_schedule (row : Vector (ZMod babyBearModulus) 9)
    (sound : (thetaRhoGeneric.table "Airbender.SplitThetaRhoGeneric").toRaw.Soundness #[] row)
    (tag : row[8] = 59) (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .thetaRho ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ column : Fin 5, row[3 + column.val] = if column.val = index.val % 5 then 1 else 0) := by
  exact theta_rho_controller_table_schedule row (theta_rho_generic_controller_sound row sound tag) active

end Airbender.Keccak.Split.Native.Fixed.Proofs
