import Airbender.Proofs.GKRProtocol.NumericPolynomialChecks

namespace Airbender.Compiler.NumericPolynomialChecks
set_option warningAsError true

def canonical (p : Nat) (polynomial : Data) : Bool :=
  polynomial.all fun term => decide (term.1 < p)

def isUnit : Data → Bool
  | [(coefficient, [])] => coefficient == 1
  | _ => false

theorem isUnit_iff (polynomial : Data) : isUnit polynomial = true ↔ polynomial = [(1, [])] := by
  cases polynomial with
  | nil => simp [isUnit]
  | cons term tail =>
      rcases term with ⟨coefficient, monomial⟩
      cases tail with
      | cons _ _ => simp [isUnit]
      | nil => cases monomial <;> simp [isUnit]

theorem multiply_unit_left (p : Nat) (polynomial : Data) (checked : canonical p polynomial = true) :
    multiply p [(1, [])] polynomial = polynomial := by
  revert checked
  induction polynomial with
  | nil => intro _; rfl
  | cons term tail ih =>
      intro checked
      simp only [canonical, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at checked
      have same := ih checked.2
      simp only [multiply, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.map_cons, Nat.one_mul, List.nil_append] at same ⊢
      rw [Nat.mod_eq_of_lt checked.1, same]

theorem multiply_unit_right (p : Nat) (polynomial : Data) (checked : canonical p polynomial = true) :
    multiply p polynomial [(1, [])] = polynomial := by
  revert checked
  induction polynomial with
  | nil => intro _; rfl
  | cons term tail ih =>
      intro checked
      simp only [canonical, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at checked
      have same := ih checked.2
      simp only [multiply, List.flatMap_cons, List.map_cons, List.map_nil,
        Nat.mul_one, List.append_nil, List.singleton_append] at same ⊢
      rw [Nat.mod_eq_of_lt checked.1, same]

/-- The range test makes each unit shortcut preserve the complete term list. -/
def fastMultiply (p : Nat) (left right : Data) : Data :=
  if isUnit left && canonical p right then right
  else if isUnit right && canonical p left then left
  else multiply p left right

theorem fastMultiply_eq (p : Nat) (left right : Data) :
    fastMultiply p left right = multiply p left right := by
  unfold fastMultiply
  split_ifs with first second
  · simp only [Bool.and_eq_true] at first
    rw [isUnit_iff] at first
    obtain ⟨rfl, checked⟩ := first
    exact (multiply_unit_left p right checked).symm
  · simp only [Bool.and_eq_true] at second
    rw [isUnit_iff] at second
    obtain ⟨rfl, checked⟩ := second
    exact (multiply_unit_right p left checked).symm
  · rfl

def initial (p inputs : Nat) (computed : Nat → Data) (wire : Nat) : Data :=
  if wire < inputs then [(1 % p, [wire])] else computed (wire - inputs)

theorem product_inputs (p inputs : Nat) (computed : Nat → Data) (monomial : List Nat)
    (primeSize : 1 < p) (inside : monomial.all (fun wire => decide (wire < inputs)) = true) :
    monomial.foldr (fun wire result => multiply p (initial p inputs computed wire) result) [(1 % p, [])] =
      [(1, monomial)] := by
  have oneMod : 1 % p = 1 := Nat.mod_eq_of_lt primeSize
  revert inside
  induction monomial with
  | nil => intro _; simp only [List.foldr_nil, oneMod]
  | cons wire tail ih =>
      intro inside
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at inside
      rw [List.foldr_cons, ih inside.2]
      simp only [initial, if_pos inside.1, oneMod,
        multiply, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
        Nat.one_mul, List.append_nil, List.singleton_append]

def fastSubstitute (p inputs : Nat) (computed : Nat → Data) (polynomial : Data) : Data :=
  polynomial.flatMap fun term =>
    if decide (1 < p) && decide (term.1 < p) && term.2.all (fun wire => decide (wire < inputs)) then [term]
    else fastMultiply p [(term.1, [])]
      (term.2.foldr (fun wire result => fastMultiply p (initial p inputs computed wire) result) [(1 % p, [])])

theorem fastSubstitute_eq (p inputs : Nat) (computed : Nat → Data) (polynomial : Data) :
    fastSubstitute p inputs computed polynomial = substitute p (initial p inputs computed) polynomial := by
  simp only [fastSubstitute, substitute, fastMultiply_eq]
  congr 1
  funext term
  split
  · rename_i checked
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    rw [product_inputs p inputs computed term.2 checked.1.1 checked.2]
    simp only [multiply, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      Nat.mul_one, Nat.mod_eq_of_lt checked.1.2, List.nil_append, List.append_nil]
  · rfl

def fastEqual (p : Nat) (left right : Data) : Bool :=
  if left == right then true else equal p left right

theorem fastEqual_eq (p : Nat) (left right : Data) : fastEqual p left right = equal p left right := by
  unfold fastEqual
  split
  · rename_i same
    have same : left = right := beq_iff_eq.mp same
    subst right
    simp only [equal, beq_self_eq_true]
  · rfl

end Airbender.Compiler.NumericPolynomialChecks
