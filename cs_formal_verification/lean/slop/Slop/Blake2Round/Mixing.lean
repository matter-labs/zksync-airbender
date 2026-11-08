module
public import Slop.Blake2Round.ColumnGQueries0
public import Slop.Blake2Round.ColumnGQueries1
public import Slop.Blake2Round.ColumnGQueries2
public import Slop.Blake2Round.ColumnGQueries3

@[expose] public section

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Each column call's sixteen table rows, four carry flags and limb equations. -/
theorem column_facts {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (columnTrace call.val w).Facts := by
  refine { toRows := ?_, toLimbs := column_limbs compatible _ w }
  fin_cases call
  exacts [column_rows_0 hp compatible h, column_rows_1 hp compatible h,
    column_rows_2 hp compatible h, column_rows_3 hp compatible h]

/-- The column calls compute Clean's G function on their prepared-state lanes,
    given 16-bit `a`, `c` and message words. -/
theorem column_g_soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : input = (columnTrace call.val w).input)
    (interface : Blake2G.InterfaceAssumptions input (columnTrace call.val w).output w) :
    Blake2G.spec input (columnTrace call.val w).output := by
  subst mapping
  exact GTrace.sound hp (column_facts hp compatible call h) interface.aBound interface.cBound
    interface.messageXBound interface.messageYBound

/-- The queries range all four column outputs, ready for the diagonal calls. -/
theorem column_g_output_bounds {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (columnTrace call.val w).output.a.Bounded ∧ (columnTrace call.val w).output.b.Bounded ∧
      (columnTrace call.val w).output.c.Bounded ∧ (columnTrace call.val w).output.d.Bounded :=
  GTrace.output_bounded (by omega) (column_facts hp compatible call h)

end Airbender.Blake2Round.Proofs
