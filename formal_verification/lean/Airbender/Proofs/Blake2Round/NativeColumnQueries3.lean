import Airbender.Proofs.Arithmetic.FieldSliceNormalization
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer
import Airbender.Proofs.Blake2Round.ArtifactChecks
import Airbender.Proofs.Constraints

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Project one native column call into the unchanged G arithmetic queries. -/
theorem native_column_queries_3 {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 18) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; exact i.isLt⟩).Contains
        (Verification.environment (nativeColumnAssignment 3 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(0 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · norm_num [carryTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, carryPad,
        ])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(1 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad, Arithmetic.carryLow_as_value,
        ] <;> ring)
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(2 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · norm_num [carryTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, carryPad,
        ])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(3 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad, Arithmetic.carryLow_as_value,
        ] <;> ring)
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(4 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply combined_high_membership hp (fun _ => Vector.replicate 7 0) member
    · norm_num [Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, combinedHighPad,
        ])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(5 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad,
        ])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(6 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply combined_low_membership hp (fun _ => Vector.replicate 7 0) member
    · norm_num [Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, combinedLowPad,
        Arithmetic.combinedLow_as_value] <;> ring)
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(7 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply combined_high_membership hp (fun _ => Vector.replicate 7 0) member
    · norm_num [Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, combinedHighPad,
        ])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(8 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad,
        ])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(9 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply combined_low_membership hp (fun _ => Vector.replicate 7 0) member
    · norm_num [Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, combinedLowPad,
        Arithmetic.combinedLow_as_value] <;> ring)
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(10 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · norm_num [carryTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, carryPad,
        ])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(11 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad, Arithmetic.carryLow_as_value,
        Arithmetic.combinedLow_as_value] <;> ring)
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(12 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · norm_num [carryTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, carryPad,
        ])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(13 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad, Arithmetic.carryLow_as_value,
        Arithmetic.combinedLow_as_value] <;> ring)
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(14 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 1 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad,
        Arithmetic.combinedLow_as_value])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(15 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad,
        ] <;> ring)
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(16 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 1 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad,
        Arithmetic.combinedLow_as_value])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) NativeLayout.legacyQuerySources[(17 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read, Blake2G.Proofs.assemble, plainPad,
        ] <;> ring)

end Airbender.Blake2Round.Proofs
