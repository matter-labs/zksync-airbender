import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.Blake2Round.Lookups

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- Rename the first invocation's actual input and temporary columns. Its output
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
  let base := columnGBase call w
  match column with
  | 17 => Blake2G.Proofs.secondAlo base
  | 18 => Blake2G.Proofs.secondAhi base
  | 21 => base 80 + 512 * base 81
  | 22 => base 82 + 512 * base 79
  | 25 => Blake2G.Proofs.secondClo base
  | 26 => Blake2G.Proofs.secondChi base
  | 29 => base 72 + 256 * base 73
  | 30 => base 74 + 256 * base 71
  | n => base n

set_option maxHeartbeats 16000000 in
/-- Each column call's twelve actual Boolean assertions and eighteen native XOR
    memberships imply the previously verified G arithmetic fragment. Assembly
    equations hold by construction of the internal output expressions. -/
theorem column_g_holds {p : Nat} [Fact p.Prime] (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (columnGAssignment call w))
      (Blake2G.Proofs.mixingConstraints (Blake2G.setupTable (fun _ => Vector.replicate 7 0))) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · intro e present
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp present
    have outputs (j : Fin 8) :
        ((FlatOperation.constraints (Blake2G.Proofs.mixingConstraints
          (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
          ⟨j.val, by rw [Blake2G.Proofs.mixing_constraint_count]; have size := j.isLt; omega⟩).eval
          (Verification.environment (columnGAssignment call w)) = 0 := by
      fin_cases j <;> simp [Blake2G.Proofs.mixingConstraints, Blake2G.importedConstraints,
        FlatOperation.constraints, Expression.eval, Verification.environment,
        columnGAssignment, columnGBase, Blake2G.Proofs.secondAlo, Blake2G.Proofs.secondAhi,
        Blake2G.Proofs.secondClo, Blake2G.Proofs.secondChi,
        Blake2G.Proofs.firstAlo, Blake2G.Proofs.firstAhi, Blake2G.Proofs.firstClo,
        Blake2G.Proofs.firstChi] <;> ring
    have carries (k : Fin 12) :
        ((FlatOperation.constraints (Blake2G.Proofs.mixingConstraints
          (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
          ⟨8 + k.val, by rw [Blake2G.Proofs.mixing_constraint_count]; have size := k.isLt; omega⟩).eval
          (Verification.environment (columnGAssignment call w)) = 0 := by
      have flag := Verification.assertion_of_holds h
        ⟨197 + 12 * call.val + k.val, by rw [constraint_count]; have size := k.isLt; have callSize := call.isLt; omega⟩
      fin_cases call <;> fin_cases k <;> simp [Blake2G.Proofs.mixingConstraints, Blake2G.importedConstraints,
        importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, columnGAssignment, columnGBase] at flag ⊢
      all_goals exact flag
    change Fin 20 at i
    by_cases early : i.val < 8
    · exact outputs ⟨i.val, early⟩
    · have equation := carries ⟨i.val - 8, by have size := i.isLt; omega⟩
      have index : 8 + (i.val - 8) = i.val := by omega
      simp only [index] at equation
      exact equation
  · intro query present
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp present
    change Fin 18 at i
    have member := Verification.lookup_of_holds h
      ⟨18 * call.val + i.val + 2, by rw [lookup_count]; have size := i.isLt; have callSize := call.isLt; omega⟩
    fin_cases call <;> fin_cases i
    all_goals apply padded_membership member
    all_goals ext j hj
    all_goals interval_cases j <;>
      simp [Expression.eval, Verification.environment, columnGAssignment, columnGBase, padXor]

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
