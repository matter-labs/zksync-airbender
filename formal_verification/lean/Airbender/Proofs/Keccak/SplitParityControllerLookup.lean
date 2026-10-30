import Airbender.Proofs.Keccak.SplitParityControllerRows

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- Both retained controller slices come from the same complete native source. -/
theorem column_parity_controller_source :
    columnParitySlotsSourceBytes = columnParityControlSourceBytes := by rfl

/-- Active native controller membership gives the original transition and selected iota round. -/
theorem column_parity_controller_table_sound [Fact babyBearModulus.Prime]
    (row : Vector (ZMod babyBearModulus) 8)
    (sound : (columnParityControl.table "Airbender.SplitColumnParityControl").toRaw.Soundness #[] row)
    (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .columnParity ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      row[3] = ((if index.val % 5 = 0 then index.val / 15 else 0 : Nat) : ZMod babyBearModulus) := by
  change ∃ i : Fin columnParityControl.length,
    row = (columnParityControl.row i).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨i, rfl⟩ := sound
  have enabled : (columnParityControl.row i)[1] = 1 := by
    rcases column_parity_controller_execute i with zero | one
    · simp [zero] at active
    · exact one
  obtain ⟨kind, before, after, round⟩ := column_parity_controller_schedule i enabled
  refine ⟨columnParityControllerIndex i, kind, ?_, ?_, ?_⟩
  · simpa only [Vector.getElem_map, Int.cast_natCast] using
      congrArg (fun value : Int => (value : ZMod babyBearModulus)) before
  · simpa only [Vector.getElem_map, Int.cast_natCast] using
      congrArg (fun value : Int => (value : ZMod babyBearModulus)) after
  · simpa only [Vector.getElem_map, Int.cast_natCast] using
      congrArg (fun value : Int => (value : ZMod babyBearModulus)) round

end Airbender.Keccak.Split.Native.Fixed.Proofs
