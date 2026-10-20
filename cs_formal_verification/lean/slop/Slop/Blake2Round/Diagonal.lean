import Slop.Blake2Round.Mixing
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- The diagonal call consumes column outputs on lanes (k,k+5,k+10,k+15).
    Existing d bytes are reused; this accounts for its two fewer allocations. -/
def diagonalGBase {p : Nat} (call : Fin 4) (w : Nat → ZMod p) (column : Nat) : ZMod p :=
  let b := Fin.ofNat 4 (call.val + 1)
  let c := Fin.ofNat 4 (call.val + 2)
  let d := Fin.ofNat 4 (call.val + 3)
  match column with
  | 15 => columnGAssignment call w 17 | 16 => columnGAssignment call w 18
  | 19 => columnGAssignment b w 21 | 20 => columnGAssignment b w 22
  | 23 => columnGAssignment c w 25 | 24 => columnGAssignment c w 26
  | 27 => columnGAssignment d w 29 | 28 => columnGAssignment d w 30
  | 33 => w (252 + 4 * call.val) | 34 => w (253 + 4 * call.val)
  | 35 => w (254 + 4 * call.val) | 36 => w (255 + 4 * call.val)
  | 43 => columnGBase d w 72 | 46 => columnGBase d w 74
  | n => if n < 43 then w (n + 415 + 44 * call.val)
    else if n < 46 then w (n + 414 + 44 * call.val)
    else w (n + 413 + 44 * call.val)

def diagonalGAssignment {p : Nat} (call : Fin 4) (w : Nat → ZMod p) : Nat → ZMod p :=
  Blake2G.Proofs.assemble (diagonalGBase call w)

set_option maxHeartbeats 20000000 in
/-- The actual diagonal queries and carries imply the same native G fragment.
    Serialized coefficient compatibility is checked, rather than assuming a
    compiler correspondence or the desired mixing result. -/
theorem diagonal_g_holds {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (diagonalGAssignment call w))
      (Blake2G.Proofs.mixingConstraints (Blake2G.setupTable (fun _ => Vector.replicate 7 0))) := by
  have field := Blake2G.Proofs.serialized_field compatible
  subst p
  unfold babyBearModulus at *
  apply Blake2G.Proofs.assembled_holds
  · intro k
    have flag := Verification.assertion_of_holds h
      ⟨245 + 12 * call.val + k.val, by rw [constraint_count]; have size := k.isLt; have callSize := call.isLt; omega⟩
    fin_cases call <;> fin_cases k
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, diagonalGBase, Blake2G.Variables.booleanColumns,
      mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
    all_goals exact flag
  · intro i
    have member := Verification.lookup_of_holds h
      ⟨74 + 18 * call.val + i.val, by rw [lookup_count]; have size := i.isLt; have callSize := call.isLt; omega⟩
    fin_cases call <;> fin_cases i
    all_goals apply padded_membership member
    all_goals ext j hj
    all_goals interval_cases j <;>
      simp [Expression.eval, Verification.environment, diagonalGBase, columnGAssignment,
        columnGBase, Blake2G.Proofs.assemble, Blake2G.Proofs.secondAlo,
        Blake2G.Proofs.secondAhi, Blake2G.Proofs.secondClo, Blake2G.Proofs.secondChi,
        Blake2G.Proofs.firstAlo, Blake2G.Proofs.firstAhi, Blake2G.Proofs.firstClo,
        Blake2G.Proofs.firstChi, padXor]
    all_goals ring_nf <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

/-- The two diagonal addition-input bounds come from column queries, not
    another interface assumption. Only the two selected message bounds remain. -/
theorem diagonal_g_input_bounds {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input} {output : Blake2G.Words}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : Blake2G.WordMapping input output (diagonalGAssignment call w)) :
    input.state.a.Bounded ∧ input.state.c.Bounded := by
  have a := Blake2G.Proofs.mixing_output_bounds hp compatible (column_g_holds call h)
  have c := Blake2G.Proofs.mixing_output_bounds hp compatible
    (column_g_holds (Fin.ofNat 4 (call.val + 2)) h)
  rw [mapping.stateReads]
  exact ⟨a.1, c.2.2.1⟩

theorem diagonal_g_soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input} {output : Blake2G.Words}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : Blake2G.WordMapping input output (diagonalGAssignment call w))
    (messageXBound : input.mx.Bounded) (messageYBound : input.my.Bounded) :
    Blake2G.spec input output := by
  have bounds := diagonal_g_input_bounds (by omega) compatible call h mapping
  exact Blake2G.Proofs.mixing_soundness hp compatible (fun _ => Vector.replicate 7 0)
    input output (diagonalGAssignment call w)
      ⟨⟨bounds.1, bounds.2, messageXBound, messageYBound⟩,
        diagonal_g_holds compatible call h, mapping⟩

theorem diagonal_g_output_bounds {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input} {output : Blake2G.Words}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : Blake2G.WordMapping input output (diagonalGAssignment call w)) :
    output.a.Bounded ∧ output.b.Bounded ∧ output.c.Bounded ∧ output.d.Bounded := by
  have bounds := Blake2G.Proofs.mixing_output_bounds hp compatible
    (diagonal_g_holds compatible call h)
  rw [mapping.stateWrites]
  exact bounds

end Airbender.Blake2Round.Proofs
