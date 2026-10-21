import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.Blake2Round.NativeColumnFlags
import Airbender.Proofs.Blake2Round.NativeColumnQueries0
import Airbender.Proofs.Blake2Round.NativeColumnQueries1
import Airbender.Proofs.Blake2Round.NativeColumnQueries2
import Airbender.Proofs.Blake2Round.NativeColumnQueries3
import Airbender.Proofs.Blake2Round.ArtifactChecks

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- The layout adapter reads native columns and splits native packed values. -/
abbrev columnGBase {p : Nat} := @nativeColumnBase p
abbrev columnGAssignment {p : Nat} := @nativeColumnAssignment p

/-- Native carry assertions and checked query projections supply the unchanged
    G arithmetic fragment. No arithmetic result is assumed. -/
theorem column_g_holds {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (columnGAssignment call w))
      (Blake2G.Proofs.mixingConstraints (Blake2G.setupTable (fun _ => Vector.replicate 7 0))) := by
  have certificate : (columnFrame call w).Certificate
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)) := by
    constructor
    · exact native_column_flags_complete hp call h
    · intro i
      fin_cases call
      · exact native_column_queries_0 hp h i
      · exact native_column_queries_1 hp h i
      · exact native_column_queries_2 hp h i
      · exact native_column_queries_3 hp h i
  exact certificate.holds

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
    input output (columnGAssignment call w) ⟨interface, column_g_holds (by omega) call h, mapping⟩

/-- These bounds are consequences of the queries, ready for the diagonal calls. -/
theorem column_g_output_bounds {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input} {output : Blake2G.Words}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : Blake2G.WordMapping input output (columnGAssignment call w)) :
    output.a.Bounded ∧ output.b.Bounded ∧ output.c.Bounded ∧ output.d.Bounded := by
  have bounds := Blake2G.Proofs.mixing_output_bounds hp compatible (column_g_holds (by omega) call h)
  rw [mapping.stateWrites]
  exact bounds

end Airbender.Blake2Round.Proofs
