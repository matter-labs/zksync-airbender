module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanIdealChecks
public import Proven.GKRProtocol.FastNumericNormalization

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanIdealRows
open NumericPolynomialChecks

structure Capture where
  ideals : CleanIdealChecks.Capture
  expanded : LookupTable Data
  combinations : LookupTable Data

structure Bindings (p : Nat) (data : Capture) : Prop where
  expanded : CleanIdealChecks.mapTable (NumericExpressionChecks.Code.polynomial p) data.ideals.codes = data.expanded
  combinations : CleanIdealChecks.mapTable (NumericArithmeticChecks.combine p data.ideals.relations)
    data.ideals.witnesses = data.combinations

def check (p : Nat) (data : Capture) : Bool :=
  CleanIdealChecks.layoutCheck data.ideals && CleanIdealChecks.scopeCheck data.ideals &&
    (List.range data.ideals.codes.size).all (fun index =>
      FastNormalization.normalize p (data.expanded.getD index [(0, [])]) ==
      FastNormalization.normalize p (data.combinations.getD index []))

theorem check_sound (p : Nat) (data : Capture) (sources : Bindings p data)
    (checked : check p data = true) :
    CleanIdealChecks.check p data.ideals = true := by
  simp only [check, Bool.and_eq_true] at checked
  have ideals : CleanIdealChecks.idealCheck p data.ideals = true := by
    apply List.all_eq_true.mpr
    intro index member
    have left := List.all_eq_true.mp checked.2 index member
    have expanded : data.expanded.getD index [(0, [])] =
        NumericExpressionChecks.Code.polynomial p (data.ideals.codes.getD index (.constant 0)) := by
      rw [← sources.expanded]
      exact CleanIdealChecks.mapTable_getD (NumericExpressionChecks.Code.polynomial p) data.ideals.codes index (.constant 0)
    have combined : data.combinations.getD index [] =
        NumericArithmeticChecks.combine p data.ideals.relations (data.ideals.witnesses.getD index []) := by
      rw [← sources.combinations]
      exact CleanIdealChecks.mapTable_getD (NumericArithmeticChecks.combine p data.ideals.relations) data.ideals.witnesses index []
    rw [expanded, combined, FastNormalization.normalize_eq, FastNormalization.normalize_eq] at left
    exact (NumericPolynomialChecks.fastEqual_eq p _ _).trans left
  simp only [CleanIdealChecks.check, Bool.and_eq_true]
  exact ⟨⟨checked.1.1, ideals⟩, checked.1.2⟩

end Airbender.Compiler.CleanIdealRows
