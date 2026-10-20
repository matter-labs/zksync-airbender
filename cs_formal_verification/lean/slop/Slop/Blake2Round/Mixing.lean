import Slop.Blake2G.Soundness
import Slop.Blake2Round.Lookups
import Slop.Blake2Round.ArtifactChecks
import Slop.Blake2Round.ColumnGFlags0
import Slop.Blake2Round.ColumnGFlags1
import Slop.Blake2Round.ColumnGFlags2
import Slop.Blake2Round.ColumnGFlags3
import Slop.Blake2Round.ColumnGQueries0
import Slop.Blake2Round.ColumnGQueries1
import Slop.Blake2Round.ColumnGQueries2
import Slop.Blake2Round.ColumnGQueries3

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

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
    fin_cases call
    exacts [column_g_flags_0 h k, column_g_flags_1 h k, column_g_flags_2 h k, column_g_flags_3 h k]
  · intro i
    fin_cases call
    exacts [column_g_queries_0 h i, column_g_queries_1 h i, column_g_queries_2 h i, column_g_queries_3 h i]

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
