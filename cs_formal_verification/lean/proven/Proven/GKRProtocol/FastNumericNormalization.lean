module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NumericPolynomialChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericPolynomialChecks.FastNormalization

theorem monomial_compare_eq (left right : List Nat) : monomialCompare left right = .eq ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [monomialCompare]
  | cons first rest ih =>
      cases right with
      | nil => simp [monomialCompare]
      | cons second tail =>
          by_cases same : first = second
          · subst second
            simpa [monomialCompare] using ih tail
          · have different : compare first second ≠ .eq := by
              intro order
              exact same (Nat.compare_eq_eq.mp order)
            cases order : compare first second with
            | eq => exact False.elim (different order)
            | lt => simp [monomialCompare, order, same]
            | gt => simp [monomialCompare, order, same]

def compareMonomial (left right : List Nat) : Ordering :=
  match left with
  | [] => match right with | [] => .eq | _ :: _ => .lt
  | first :: rest => match right with
    | [] => .gt
    | second :: tail =>
        if first == second then compareMonomial rest tail
        else if first < second then .lt else .gt
termination_by structural left

theorem compareMonomial_eq (left right : List Nat) : compareMonomial left right = monomialCompare left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons first rest ih =>
      cases right with
      | nil => rfl
      | cons second tail =>
          cases order : compare first second with
          | eq =>
              have same := Nat.compare_eq_eq.mp order
              subst second
              simp only [compareMonomial, monomialCompare, beq_self_eq_true, ite_true, order, ih]
          | lt =>
              have less := Nat.compare_eq_lt.mp order
              have different := Nat.ne_of_lt less
              simp [compareMonomial, monomialCompare, different, less, order]
          | gt =>
              have greater := Nat.compare_eq_gt.mp order
              have different := Nat.ne_of_gt greater
              simp [compareMonomial, monomialCompare, different, Nat.not_lt_of_gt greater, order]

def insert (p : Nat) (term : Nat × List Nat) (polynomial : Data) : Data :=
  if term.1 == 0 then polynomial
  else match polynomial with
    | [] => [term]
    | head :: tail => match compareMonomial term.2 head.2 with
      | .eq =>
          let sum := (term.1 + head.1) % p
          if sum == 0 then tail else (sum, term.2) :: tail
      | .lt => term :: head :: tail
      | .gt => head :: insert p term tail
termination_by structural polynomial

theorem insert_eq (p : Nat) (term : Nat × List Nat) (polynomial : Data) :
    insert p term polynomial = insertTerm p term polynomial := by
  induction polynomial with
  | nil => simp only [insert, insertTerm]
  | cons head tail ih =>
      by_cases zero : term.1 = 0
      · simp [insert, insertTerm, zero]
      · by_cases same : term.2 = head.2
        · have self := (monomial_compare_eq head.2 head.2).mpr rfl
          simp [insert, compareMonomial_eq, insertTerm, zero, same, self]
        · have different : monomialCompare term.2 head.2 ≠ .eq := by
            intro order
            exact same ((monomial_compare_eq term.2 head.2).mp order)
          cases order : monomialCompare term.2 head.2 with
          | eq => exact False.elim (different order)
          | lt => simp [insert, compareMonomial_eq, insertTerm, zero, same, order]
          | gt => simp [insert, compareMonomial_eq, insertTerm, zero, same, order, ih]

def normalize (p : Nat) (polynomial : Data) : Data :=
  polynomial.foldr (fun term result => insert p (term.1, term.2.insertionSort (fun a b => a ≤ b)) result) []

theorem normalize_eq (p : Nat) (polynomial : Data) :
    normalize p polynomial = NumericPolynomialChecks.normalize p polynomial := by
  simp only [normalize, NumericPolynomialChecks.normalize, insert_eq]

theorem map_eq (p : Nat) (polynomials : List Data) :
    polynomials.map (normalize p) = polynomials.map (NumericPolynomialChecks.normalize p) := by
  apply List.map_congr_left
  intro polynomial _
  exact normalize_eq p polynomial

end Airbender.Compiler.NumericPolynomialChecks.FastNormalization
