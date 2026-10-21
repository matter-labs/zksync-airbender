import Airbender.Proofs.Blake2Round.DiagonalBase
import Airbender.Proofs.Blake2Round.NativeDiagonalFacts
import Airbender.Proofs.Blake2Round.NativeDiagonalQueries0

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Native acceptance constructs the shared G frame certificate. -/
theorem diagonal_g_holds_0 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (diagonalGAssignment 0 w))
      (Blake2G.Proofs.mixingConstraints (Blake2G.setupTable (fun _ => Vector.replicate 7 0))) := by
  have field := Blake2G.Proofs.serialized_field compatible
  have hp : 262144 ≤ p := by rw [field]; decide
  have queries := native_diagonal_queries_0 (by omega) compatible h
  have certificate : (diagonalFrame 0 w).Certificate
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)) :=
    ⟨native_diagonal_flags_complete hp compatible 0 h queries, queries⟩
  exact certificate.holds

end Airbender.Blake2Round.Proofs
