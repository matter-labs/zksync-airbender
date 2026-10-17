import Tests.UnifiedDelegationShared
namespace Tests.UnifiedDelegationNormalization
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option Elab.async false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
abbrev assignment (one : Bool) (stage : Fin 2) (column : Nat) : ZMod babyBearModulus :=
  if stage = 0 then
    if column = 0 then 4
    else if column = 2 || column = 30 || column = 46 then 8
    else if column = 32 || column = 5 || column = 7 || column = 44 then 12
    else if column = 34 then 7
    else if column = 40 then 6
    else if column = 36 || column = 48 || column = 74 || column = 93 then if one then 1 else 0
    else if column = 10 || column = 92 || column = 101 || column = 110 || column = 119 then 53
    else if column = 88 then 3
    else if column = 4 || column = 8 || column = 27 || column = 50 || column = 58 || column = 94 || column = 95 ||
        column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
    else 0
  else
    if column = 0 then 8
    else if column = 2 || column = 30 || column = 5 || column = 7 || column = 44 || column = 46 then 12
    else if column = 32 then 16
    else if column = 34 then 10
    else if column = 40 then 9
    else if column = 8 then 127
    else if column = 50 then 128
    else if column = 4 || column = 11 || column = 36 || column = 48 ||
        column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
    else 0
theorem fixedMember (initial : State) (index : Fin 524545)
    (value : Vector (ZMod babyBearModulus) 10)
    (equal : value = ((Verification.referenceShiftBinopRow index).set 9
      (UnifiedReduced.Setup.binaryTag (Verification.referenceShiftBinopRow index)[9])).map
        (fun n : Nat => (n : ZMod babyBearModulus))) :
    (UnifiedReduced.Setup.table initial).Contains #[] value := by
  change ∃ i : Fin 2097537, _
  refine ⟨⟨index.val, by have bound := index.isLt; omega⟩, ?_⟩
  dsimp only
  rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
  have fixedBound : index.val < 1048961 := by have := index.isLt; omega
  simpa only [UnifiedReduced.Setup.referenceRow, dif_pos fixedBound,
    UnifiedReduced.Setup.referenceFixedRow, dif_pos index.isLt,
    UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference] using equal

theorem constraints (state : State) (one : Bool) (stage : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment one stage)) (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table state)) := by
  cases one <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, assignment, Lookup.Contains, Table.toRaw, fromElements,
    UnifiedReduced.Setup.table, UnifiedReduced.Setup.tableOfRows]
  all_goals repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (apply fixedMember _ (⟨0, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | (apply fixedMember _ (⟨1, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | (apply fixedMember _ (⟨65793, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | (apply fixedMember _ (⟨65794, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | (apply fixedMember _ (⟨66050, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | decide +kernel
end Tests.UnifiedDelegationNormalization
