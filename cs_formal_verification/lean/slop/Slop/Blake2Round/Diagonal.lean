import Slop.Blake2Round.Mixing
import Slop.Blake2Round.DiagonalG
import Slop.Blake2Round.DiagonalGFlags0
import Slop.Blake2Round.DiagonalGFlags1
import Slop.Blake2Round.DiagonalGFlags2
import Slop.Blake2Round.DiagonalGFlags3
import Slop.Blake2Round.DiagonalGQueries0
import Slop.Blake2Round.DiagonalGQueries1
import Slop.Blake2Round.DiagonalGQueries2
import Slop.Blake2Round.DiagonalGQueries3

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- The actual diagonal queries and carries imply the same native G fragment.
    Serialized coefficient compatibility is checked, rather than assuming a
    compiler correspondence or the desired mixing result. -/
theorem diagonal_g_holds {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (diagonalGAssignment call w))
      (Blake2G.Proofs.mixingConstraints (Blake2G.setupTable (fun _ => Vector.replicate 7 0))) := by
  apply Blake2G.Proofs.assembled_holds
  · intro k
    fin_cases call
    exacts [diagonal_g_flags_0 compatible h k, diagonal_g_flags_1 compatible h k,
      diagonal_g_flags_2 compatible h k, diagonal_g_flags_3 compatible h k]
  · intro i
    fin_cases call
    exacts [diagonal_g_queries_0 compatible h i, diagonal_g_queries_1 compatible h i,
      diagonal_g_queries_2 compatible h i, diagonal_g_queries_3 compatible h i]

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
