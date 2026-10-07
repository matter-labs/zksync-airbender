import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.Blake2Round.Lookups

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- Rename each column invocation's actual input and temporary columns. Its output
-- words are expressions in this artifact, not separate allocated variables.
def columnGBase {p : Nat} (call : Fin 4) (w : Nat → ZMod p) (column : Nat) : ZMod p :=
  match column with
  | 15 => w (155 + 4 * call.val) | 16 => w (157 + 4 * call.val)
  | 19 => w (171 + 4 * call.val) | 20 => w (173 + 4 * call.val)
  | 23 => w (186 + 2 * call.val) | 24 => w (187 + 2 * call.val)
  | 27 => w (#v[198, 194, 200, 196][call]) | 28 => w (#v[199, 195, 201, 197][call])
  | 33 => w (236 + 4 * call.val) | 34 => w (237 + 4 * call.val)
  | 35 => w (238 + 4 * call.val) | 36 => w (239 + 4 * call.val)
  | n => w (n + 231 + 46 * call.val)

def columnGAssignment {p : Nat} (call : Fin 4) (w : Nat → ZMod p) (column : Nat) : ZMod p :=
  Blake2G.Proofs.assemble (columnGBase call w) column

set_option maxHeartbeats 16000000 in
/-- Each column call's twelve actual Boolean assertions and eighteen native XOR
    memberships imply the previously verified G arithmetic fragment. Assembly
    equations hold by construction of the internal output expressions. -/
theorem column_g_holds {p : Nat} [Fact p.Prime] (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (columnGAssignment call w))
      (Blake2G.Proofs.mixingConstraints (Blake2G.setupTable (fun _ => Vector.replicate 7 0))) := by
  apply Blake2G.Proofs.assembled_holds
  · intro k
    have flag := Verification.assertion_of_holds h
      ⟨197 + 12 * call.val + k.val, by rw [constraint_count]; have size := k.isLt; have callSize := call.isLt; omega⟩
    fin_cases call <;> fin_cases k
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, columnGBase, Blake2G.Variables.booleanColumns,
      mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
    all_goals exact flag
  · intro i
    have member := Verification.lookup_of_holds h
      ⟨18 * call.val + i.val + 2, by rw [lookup_count]; have size := i.isLt; have callSize := call.isLt; omega⟩
    fin_cases call <;> fin_cases i
    all_goals apply padded_membership member
    all_goals ext j hj
    all_goals interval_cases j <;>
      simp [Expression.eval, Verification.environment, columnGBase, Blake2G.Proofs.assemble, padXor]

/-- Reuse the same G soundness theorem for all four column calls. The mapping
    selects their internal input/output expressions; it assumes no G result. -/
theorem column_g_soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input} {output : Blake2G.Words}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : Blake2G.WordMapping input output (columnGAssignment call w))
    (interface : Blake2G.InterfaceAssumptions input output (columnGAssignment call w)) :
    Blake2G.spec input output :=
  Blake2G.Proofs.mixing_soundness hp compatible (fun _ => Vector.replicate 7 0)
    input output (columnGAssignment call w) ⟨interface, column_g_holds call h, mapping⟩

/-- These bounds are consequences of the queries, ready for the diagonal calls. -/
theorem column_g_output_bounds {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input} {output : Blake2G.Words}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : Blake2G.WordMapping input output (columnGAssignment call w)) :
    output.a.Bounded ∧ output.b.Bounded ∧ output.c.Bounded ∧ output.d.Bounded := by
  have bounds := Blake2G.Proofs.mixing_output_bounds hp compatible (column_g_holds call h)
  rw [mapping.stateWrites]
  exact bounds

end Airbender.Blake2Round.Proofs
