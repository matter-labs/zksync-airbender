module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NumericArithmeticChecks
public import Proven.GKRProtocol.PackedNormalizationTrace

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericArithmeticTrace
open NumericPolynomialChecks
open PackedNormalization

def rowBindingCheck (pair : Data × Data) (row : PolynomialRow) : Bool :=
  (pack (KeyedNormalization.encodeRows pair.1) == row.expected) &&
  (pack (KeyedNormalization.encodeRows pair.2) == row.input) &&
  pair.1.all (fun term => KeyedNormalization.sortedSmall term.2) &&
  pair.2.all (fun term => KeyedNormalization.small term.2) &&
  boundsCheck (KeyedNormalization.encodeRows pair.1) &&
  boundsCheck (KeyedNormalization.encodeRows pair.2)

theorem rowBindingCheck_sound (pair : Data × Data) (row : PolynomialRow)
    (checked : rowBindingCheck pair row = true) : row.Binding pair.1 pair.2 := by
  simp only [rowBindingCheck, Bool.and_eq_true, beq_iff_eq] at checked
  rcases checked with ⟨⟨⟨⟨⟨expected, input⟩, sorted⟩, small⟩, expectedBounds⟩, inputBounds⟩
  exact ⟨expected, input, sorted, small, boundsCheck_sound _ expectedBounds, boundsCheck_sound _ inputBounds⟩

def bindingCheck (pairs : List (Data × Data)) (rows : List PolynomialRow) : Bool :=
  (pairs.length == rows.length) && (pairs.zip rows).all (fun (pair, row) => rowBindingCheck pair row)

theorem bindingCheck_sound (pairs : List (Data × Data)) (rows : List PolynomialRow)
    (checked : bindingCheck pairs rows = true) :
    List.Forall₂ (fun pair row => row.Binding pair.1 pair.2) pairs rows := by
  induction pairs generalizing rows with
  | nil =>
      cases rows with
      | nil => exact .nil
      | cons _ _ => simp [bindingCheck] at checked
  | cons pair pairs ih =>
      cases rows with
      | nil => simp [bindingCheck] at checked
      | cons row rows =>
          simp only [bindingCheck, List.length_cons, List.zip_cons_cons, List.all_cons,
            Bool.and_eq_true, beq_iff_eq, Nat.add_right_cancel_iff] at checked
          exact .cons (rowBindingCheck_sound pair row checked.2.1)
            (ih rows (by
              simp only [bindingCheck, Bool.and_eq_true, beq_iff_eq]
              exact ⟨checked.1, checked.2.2⟩))

theorem checked_pairs (p : Nat) (pairs : List (Data × Data)) (rows : List PolynomialRow)
    (binding : bindingCheck pairs rows = true) (checked : PackedNormalization.check p rows = true) :
    pairs.all (fun (expected, input) => NumericPolynomialChecks.normalize p input == expected) = true := by
  have relation := bindingCheck_sound pairs rows binding
  simp only [PackedNormalization.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
  clear binding
  induction relation with
  | nil => rfl
  | @cons pair row pairs rows rowBound rest ih =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq]
      constructor
      · exact PolynomialRow.check_sound p checked.1.1 checked.1.2 pair.1 pair.2 row rowBound (checked.2 row (by simp))
      · exact ih ⟨checked.1, fun item member => checked.2 item (by simp [member])⟩

def forwardExpected (p : Nat) (data : NumericArithmeticChecks.Capture inputs)
    (terms : List (Data × Nat)) : Data :=
  match terms with
  | [(factor, index)] =>
      if isUnit factor && canonical p (data.sourceRows.getD index []) then data.normalizedSourceRows.getD index []
      else NumericPolynomialChecks.normalize p (NumericArithmeticChecks.combine p data.sourceRows terms)
  | _ => NumericPolynomialChecks.normalize p (NumericArithmeticChecks.combine p data.sourceRows terms)

theorem forwardExpected_eq (p : Nat) (data : NumericArithmeticChecks.Capture inputs)
    (polynomial : Data) (terms : List (Data × Nat)) :
    NumericArithmeticChecks.forwardEqual p data polynomial terms =
      (NumericPolynomialChecks.normalize p polynomial == forwardExpected p data terms) := by
  cases terms with
  | nil => exact fastEqual_eq ..
  | cons term rest =>
      cases rest with
      | cons _ _ => exact fastEqual_eq ..
      | nil =>
          rcases term with ⟨factor, index⟩
          simp only [NumericArithmeticChecks.forwardEqual, forwardExpected]
          split
          · rfl
          · exact fastEqual_eq ..

def pairs (p : Nat) (data : NumericArithmeticChecks.Capture inputs) : List (Data × Data) :=
  (List.range data.sourceRows.size).map (fun index =>
    (data.normalizedSourceRows.getD index [], NumericArithmeticChecks.combine p data.lowerRows (data.backwardRows.getD index []))) ++
  (List.range data.lowerRows.size).map (fun index =>
    (forwardExpected p data (data.forwardRows.getD index []),
     fastSubstitute p inputs (fun index => data.computedRows.getD index []) (data.lowerRows.getD index [])))

structure Capture (inputs : Nat) where
  numeric : NumericArithmeticChecks.Capture inputs
  rows : List PolynomialRow

def check (p : Nat) (data : Capture inputs) : Bool :=
  NumericArithmeticChecks.layoutCheck data.numeric &&
    AddressUniqueChecks.ascending data.numeric.sortedAddressKeys &&
    NumericArithmeticChecks.gateCheck data.numeric && PackedNormalization.check p data.rows

theorem check_sound (p : Nat) (data : Capture inputs)
    (binding : bindingCheck (pairs p data.numeric) data.rows = true)
    (checked : check p data = true) : NumericArithmeticChecks.check p data.numeric = true := by
  simp only [check, Bool.and_eq_true] at checked
  have normalized := checked_pairs p _ _ binding checked.2
  simp only [pairs, List.all_append, List.all_map, Function.comp_def, Bool.and_eq_true] at normalized
  simp only [NumericArithmeticChecks.check, NumericArithmeticChecks.translationCheck, Bool.and_eq_true]
  exact ⟨⟨⟨checked.1.1.1, checked.1.1.2⟩,
    ⟨by simpa only [BEq.comm] using normalized.1,
     by simpa only [forwardExpected_eq] using normalized.2⟩⟩, checked.1.2⟩

end Airbender.Compiler.NumericArithmeticTrace
