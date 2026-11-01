import Airbender.Proofs.GKRProtocol.CleanIdealChecks
import Airbender.Proofs.GKRProtocol.ArithmeticNormalizationTrace

namespace Airbender.Compiler.CleanIdealTrace
open NumericPolynomialChecks
set_option warningAsError true

structure Capture where
  ideals : CleanIdealChecks.Capture
  normalized : LookupTable Data
  expanded : LookupTable Data
  combinations : LookupTable Data
  rows : List PackedNormalization.PolynomialRow

def pairs (_p : Nat) (data : Capture) : List (Data × Data) :=
  (List.range data.ideals.codes.size).map (fun index =>
    (data.normalized.getD index [], data.expanded.getD index [(0, [])])) ++
  (List.range data.ideals.codes.size).map (fun index =>
    (data.normalized.getD index [], data.combinations.getD index []))

structure Bindings (p : Nat) (data : Capture) : Prop where
  expanded : CleanIdealChecks.mapTable (NumericExpressionChecks.Code.polynomial p) data.ideals.codes = data.expanded
  combinations : CleanIdealChecks.mapTable (NumericArithmeticChecks.combine p data.ideals.relations)
    data.ideals.witnesses = data.combinations

def bindingCheck (p : Nat) (data : Capture) : Bool :=
  NumericArithmeticTrace.bindingCheck (pairs p data) data.rows

def check (p : Nat) (data : Capture) : Bool :=
  CleanIdealChecks.layoutCheck data.ideals && CleanIdealChecks.scopeCheck data.ideals &&
    data.normalized.valid && (data.normalized.size == data.ideals.codes.size) &&
    PackedNormalization.check p data.rows

theorem check_sound (p : Nat) (data : Capture) (sources : Bindings p data)
    (binding : bindingCheck p data = true) (checked : check p data = true) :
    CleanIdealChecks.check p data.ideals = true := by
  simp only [check, Bool.and_eq_true] at checked
  have normalized := NumericArithmeticTrace.checked_pairs p _ _ binding checked.2
  simp only [pairs, List.all_append, List.all_map, Function.comp_def, Bool.and_eq_true] at normalized
  have ideals : CleanIdealChecks.idealCheck p data.ideals = true := by
    apply List.all_eq_true.mpr
    intro index member
    have left := List.all_eq_true.mp normalized.1 index member
    have right := List.all_eq_true.mp normalized.2 index member
    have expanded : data.expanded.getD index [(0, [])] =
        NumericExpressionChecks.Code.polynomial p (data.ideals.codes.getD index (.constant 0)) := by
      rw [← sources.expanded]
      exact CleanIdealChecks.mapTable_getD (NumericExpressionChecks.Code.polynomial p) data.ideals.codes index (.constant 0)
    have combined : data.combinations.getD index [] =
        NumericArithmeticChecks.combine p data.ideals.relations (data.ideals.witnesses.getD index []) := by
      rw [← sources.combinations]
      exact CleanIdealChecks.mapTable_getD (NumericArithmeticChecks.combine p data.ideals.relations) data.ideals.witnesses index []
    rw [expanded] at left
    rw [combined] at right
    rw [beq_iff_eq] at left right
    rw [NumericPolynomialChecks.fastEqual_eq, NumericPolynomialChecks.equal, left, right]
    exact beq_self_eq_true _
  simp only [CleanIdealChecks.check, Bool.and_eq_true]
  exact ⟨⟨checked.1.1.1.1, ideals⟩, checked.1.1.1.2⟩

end Airbender.Compiler.CleanIdealTrace
