import Airbender.Proofs.Blake2G.FrameNormalization
import Airbender.Proofs.Blake2G.Soundness
import Mathlib.Tactic.ReduceModChar
import Airbender.Proofs.Arithmetic.FieldSliceNormalization
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer
import Airbender.Proofs.Blake2Round.ArtifactChecks
import Airbender.Proofs.Constraints

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Project one native diagonal call into the unchanged G arithmetic queries. -/
theorem native_diagonal_queries_3_part_1 {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 3) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨3 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeDiagonalAssignment 3 w)) := by
  have field := Blake2G.Proofs.serialized_field compatible
  subst p
  unfold babyBearModulus at *
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) NativeLayout.legacyQuerySources[(3 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [importedConstraints, FlatOperation.lookups, nativeDiagonalAssignment, diagonalFrame, diagonalIncoming, NativeLayout.diagonal,
        NativeLayout.queryColumn, NativeLayout.queryIndex,


         Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment_eq_normalized, Blake2G.Proofs.Frame.normalizedAssignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read,  plainPad, Arithmetic.carryLow_as_value,
        ] <;> ring_nf <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char)
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) NativeLayout.legacyQuerySources[(4 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply combined_high_membership hp (fun _ => Vector.replicate 7 0) member
    · norm_num [Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [importedConstraints, FlatOperation.lookups, nativeDiagonalAssignment, diagonalFrame, diagonalIncoming, NativeLayout.diagonal,
        NativeLayout.queryColumn, NativeLayout.queryIndex,


         Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment_eq_normalized, Blake2G.Proofs.Frame.normalizedAssignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read,  combinedHighPad,
        ])
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (3 : Fin 4) NativeLayout.legacyQuerySources[(5 : Fin 18)], by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · norm_num [plainTags, Expression.eval]
    · ext j hj
      interval_cases j
      all_goals (simp [importedConstraints, FlatOperation.lookups, nativeDiagonalAssignment, diagonalFrame, diagonalIncoming, NativeLayout.diagonal,
        NativeLayout.queryColumn, NativeLayout.queryIndex,


         Expression.eval, Verification.environment, nativeColumnAssignment, Blake2G.Proofs.Frame.assignment_eq_normalized, Blake2G.Proofs.Frame.normalizedAssignment, Blake2G.Proofs.Frame.base, columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read,  plainPad,
        ])

end Airbender.Blake2Round.Proofs
