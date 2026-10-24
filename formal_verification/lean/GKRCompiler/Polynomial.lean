import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

/- Computable sparse polynomials for kernel-checked translation certificates.
The normalizer needs no uniqueness theorem: preserving evaluation and comparing
its concrete output suffices for a sound equality checker. -/
namespace Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

abbrev Monomial (arity : Nat) := List (Fin arity)
abbrev Polynomial (arity : Nat) (F : Type) := List (F × Monomial arity)

def monomialValue [CommRing F] (values : Fin n → F) (monomial : Monomial n) : F :=
  (monomial.map values).prod

def evaluate [CommRing F] (values : Fin n → F) (polynomial : Polynomial n F) : F :=
  (polynomial.map fun term => term.1 * monomialValue values term.2).sum

def constant [CommRing F] (value : F) : Polynomial n F := [(value, [])]
def atom [CommRing F] (wire : Fin n) : Polynomial n F := [(1, [wire])]
def add (left right : Polynomial n F) : Polynomial n F := left ++ right
def negate [CommRing F] (polynomial : Polynomial n F) : Polynomial n F :=
  polynomial.map fun term => (-term.1, term.2)
def multiply [CommRing F] (left right : Polynomial n F) : Polynomial n F :=
  left.flatMap fun a => right.map fun b => (a.1 * b.1, a.2 ++ b.2)
def rename (placement : Fin n → Fin m) (polynomial : Polynomial n F) : Polynomial m F :=
  polynomial.map fun term => (term.1, term.2.map placement)

@[simp] theorem monomial_nil [CommRing F] (values : Fin n → F) :
    monomialValue values [] = 1 := rfl

@[simp] theorem monomial_cons [CommRing F] (values : Fin n → F) (wire : Fin n) (rest) :
    monomialValue values (wire :: rest) = values wire * monomialValue values rest := rfl

theorem monomial_append [CommRing F] (values : Fin n → F) (left right : Monomial n) :
    monomialValue values (left ++ right) = monomialValue values left * monomialValue values right := by
  simp [monomialValue, List.map_append, List.prod_append]

@[simp] theorem evaluate_nil [CommRing F] (values : Fin n → F) :
    evaluate values ([] : Polynomial n F) = 0 := rfl

@[simp] theorem evaluate_cons [CommRing F] (values : Fin n → F) (term) (rest) :
    evaluate values (term :: rest) = term.1 * monomialValue values term.2 + evaluate values rest := rfl

@[simp] theorem evaluate_constant [CommRing F] (values : Fin n → F) (value : F) :
    evaluate values (constant value) = value := by simp [constant]

@[simp] theorem evaluate_atom [CommRing F] (values : Fin n → F) (wire : Fin n) :
    evaluate values (atom wire) = values wire := by simp [atom]

@[simp] theorem evaluate_add [CommRing F] (values : Fin n → F) (left right : Polynomial n F) :
    evaluate values (add left right) = evaluate values left + evaluate values right := by
  simp [evaluate, add, List.map_append, List.sum_append]

@[simp] theorem evaluate_append [CommRing F] (values : Fin n → F) (left right : Polynomial n F) :
    evaluate values (left ++ right) = evaluate values left + evaluate values right :=
  evaluate_add values left right

@[simp] theorem evaluate_negate [CommRing F] (values : Fin n → F) (polynomial : Polynomial n F) :
    evaluate values (negate polynomial) = -evaluate values polynomial := by
  induction polynomial with
  | nil => simp [negate]
  | cons term rest ih =>
    change -term.1 * monomialValue values term.2 + evaluate values (negate rest) = _
    rw [ih, evaluate_cons]
    ring

@[simp] theorem evaluate_multiply [CommRing F] (values : Fin n → F) (left right : Polynomial n F) :
    evaluate values (multiply left right) = evaluate values left * evaluate values right := by
  have row (term : F × Monomial n) (items : Polynomial n F) :
      evaluate values (items.map (fun b => (term.1 * b.1, term.2 ++ b.2))) =
      term.1 * monomialValue values term.2 * evaluate values items := by
    induction items with
    | nil => simp
    | cons b tail ih =>
      simp only [List.map_cons, evaluate_cons, monomial_append, ih]
      ring
  induction left with
  | nil => simp [multiply]
  | cons term rest ih =>
    change evaluate values
      (right.map (fun b => (term.1 * b.1, term.2 ++ b.2)) ++ multiply rest right) = _
    rw [evaluate_append, row, ih, evaluate_cons]
    ring

@[simp] theorem evaluate_rename [CommRing F] (values : Fin m → F) (placement : Fin n → Fin m)
    (polynomial : Polynomial n F) :
    evaluate values (rename placement polynomial) = evaluate (values ∘ placement) polynomial := by
  simp [evaluate, rename, monomialValue, List.map_map, Function.comp_def]

def insertTerm [CommRing F] [DecidableEq F] (term : F × Monomial n) :
    Polynomial n F → Polynomial n F
  | [] => if term.1 = 0 then [] else [term]
  | head :: tail =>
      if term.1 = 0 then head :: tail
      else if term.2 = head.2 then
        if term.1 + head.1 = 0 then tail else (term.1 + head.1, term.2) :: tail
      else if compare term.2 head.2 == .lt then term :: head :: tail
      else head :: insertTerm term tail

theorem evaluate_insertTerm [CommRing F] [DecidableEq F] (values : Fin n → F)
    (term : F × Monomial n) (polynomial : Polynomial n F) :
    evaluate values (insertTerm term polynomial) =
      term.1 * monomialValue values term.2 + evaluate values polynomial := by
  induction polynomial with
  | nil => simp [insertTerm]; split_ifs <;> simp_all
  | cons head tail ih =>
    simp only [insertTerm]
    split_ifs with zero same sumZero earlier
    · simp [zero]
    · simp only [evaluate_cons]
      rw [← same]
      rw [← add_assoc, ← add_mul, sumZero, zero_mul, zero_add]
    · simp only [evaluate_cons]
      rw [← same]
      ring
    · rfl
    · simp only [evaluate_cons, ih]
      ring

def normalize [CommRing F] [DecidableEq F] (polynomial : Polynomial n F) : Polynomial n F :=
  polynomial.foldr (fun term result =>
    insertTerm (term.1, term.2.insertionSort (fun a b => a.val ≤ b.val)) result) []

theorem evaluate_normalize [CommRing F] [DecidableEq F] (values : Fin n → F)
    (polynomial : Polynomial n F) : evaluate values (normalize polynomial) = evaluate values polynomial := by
  induction polynomial with
  | nil => rfl
  | cons term rest ih =>
    simp only [normalize, List.foldr_cons, evaluate_insertTerm, evaluate_cons]
    have ordered : monomialValue values
        (term.2.insertionSort (fun a b => a.val ≤ b.val)) = monomialValue values term.2 := by
      exact List.Perm.prod_eq ((List.perm_insertionSort _ _).map values)
    rw [ordered]
    exact congrArg (fun value => term.1 * monomialValue values term.2 + value) ih

def equal [CommRing F] [DecidableEq F] (left right : Polynomial n F) : Bool :=
  decide (normalize left = normalize right)

theorem equal_sound [CommRing F] [DecidableEq F] {left right : Polynomial n F}
    (checked : equal left right = true) (values : Fin n → F) :
    evaluate values left = evaluate values right := by
  have same : normalize left = normalize right := of_decide_eq_true checked
  rw [← evaluate_normalize values left, ← evaluate_normalize values right, same]

def substitute [CommRing F] (extension : Fin m → Polynomial n F) (polynomial : Polynomial m F) :
    Polynomial n F :=
  polynomial.flatMap fun term =>
    multiply (constant term.1) (term.2.foldr (fun wire result => multiply (extension wire) result) (constant 1))

@[simp] theorem evaluate_substitute [CommRing F] (values : Fin n → F)
    (extension : Fin m → Polynomial n F) (polynomial : Polynomial m F) :
    evaluate values (substitute extension polynomial) =
      evaluate (fun wire => evaluate values (extension wire)) polynomial := by
  have product (monomial : Monomial m) : evaluate values
      (monomial.foldr (fun wire result => multiply (extension wire) result) (constant 1)) =
      monomialValue (fun wire => evaluate values (extension wire)) monomial := by
    induction monomial with
    | nil => simp
    | cons wire rest ih => simp [ih]
  induction polynomial with
  | nil => rfl
  | cons term rest ih =>
    change evaluate values
      (multiply (constant term.1)
        (term.2.foldr (fun wire result => multiply (extension wire) result) (constant 1)) ++
        substitute extension rest) = _
    rw [evaluate_append, evaluate_multiply, evaluate_constant, product, ih, evaluate_cons]

end Airbender.Compiler
