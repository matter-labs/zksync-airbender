import Airbender.Proofs.Blake2Round.DiagonalBase

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

/-- One actual diagonal call, checked separately to bound compilation memory. -/
theorem diagonal_g_holds_1 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (diagonalGAssignment (1 : Fin 4) w))
      (Blake2G.Proofs.mixingConstraints (Blake2G.setupTable (fun _ => Vector.replicate 7 0))) := by
  have field := Blake2G.Proofs.serialized_field compatible
  subst p
  unfold babyBearModulus at *
  apply Blake2G.Proofs.assembled_holds
  · intro k
    have flag := Verification.assertion_of_holds h
      ⟨245 + 12 * (1 : Fin 4).val + k.val, by rw [constraint_count]; have size := k.isLt; have callSize := (1 : Fin 4).isLt; omega⟩
    clear h
    fin_cases k
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, diagonalGBase, Blake2G.Variables.booleanColumns,
      mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
    all_goals exact flag
  · intro i
    have member := Verification.lookup_of_holds h
      ⟨74 + 18 * (1 : Fin 4).val + i.val, by rw [lookup_count]; have size := i.isLt; have callSize := (1 : Fin 4).isLt; omega⟩
    clear h
    fin_cases i
    all_goals apply padded_membership member
    all_goals ext j hj
    all_goals interval_cases j <;>
      simp [Expression.eval, Verification.environment, diagonalGBase, columnGAssignment,
        columnGBase, Blake2G.Proofs.assemble, Blake2G.Proofs.secondAlo,
        Blake2G.Proofs.secondAhi, Blake2G.Proofs.secondClo, Blake2G.Proofs.secondChi,
        Blake2G.Proofs.firstAlo, Blake2G.Proofs.firstAhi, Blake2G.Proofs.firstClo,
        Blake2G.Proofs.firstChi, padXor]
    all_goals ring_nf <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

end Airbender.Blake2Round.Proofs
