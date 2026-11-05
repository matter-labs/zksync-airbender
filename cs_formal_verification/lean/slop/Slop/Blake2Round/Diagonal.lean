import Slop.Blake2Round.Mixing
import Slop.Blake2Round.DiagonalGQueries0
import Slop.Blake2Round.DiagonalGQueries1
import Slop.Blake2Round.DiagonalGQueries2
import Slop.Blake2Round.DiagonalGQueries3

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Each diagonal call's sixteen table rows, two carry flags and limb equations. -/
theorem diagonal_facts {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (diagonalTrace call.val w).Facts := by
  refine { toRows := ?_, toLimbs := diagonal_limbs compatible _ w }
  fin_cases call
  exacts [diagonal_rows_0 hp compatible h, diagonal_rows_1 hp compatible h,
    diagonal_rows_2 hp compatible h, diagonal_rows_3 hp compatible h]

/-- The two diagonal addition inputs are column outputs, ranged by the column
    queries, not another interface assumption. -/
theorem diagonal_g_input_bounds {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (diagonalTrace call.val w).input.state.a.Bounded ∧
      (diagonalTrace call.val w).input.state.c.Bounded := by
  have a := column_g_output_bounds hp compatible call h
  have c := column_g_output_bounds hp compatible (Fin.ofNat 4 (call.val + 2)) h
  exact ⟨a.1, c.2.2.1⟩

/-- The diagonal calls compute Clean's G function on the column outputs; only
    the two selected message bounds remain external. -/
theorem diagonal_g_soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : input = (diagonalTrace call.val w).input)
    (messageXBound : input.mx.Bounded) (messageYBound : input.my.Bounded) :
    Blake2G.spec input (diagonalTrace call.val w).output := by
  subst mapping
  have bounds := diagonal_g_input_bounds hp compatible call h
  exact GTrace.sound hp (diagonal_facts hp compatible call h) bounds.1 bounds.2
    messageXBound messageYBound

/-- The queries range all four diagonal outputs, which are the write columns. -/
theorem diagonal_g_output_bounds {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (diagonalTrace call.val w).output.a.Bounded ∧ (diagonalTrace call.val w).output.b.Bounded ∧
      (diagonalTrace call.val w).output.c.Bounded ∧ (diagonalTrace call.val w).output.d.Bounded :=
  GTrace.output_bounded (by omega) (diagonal_facts hp compatible call h)

end Airbender.Blake2Round.Proofs
