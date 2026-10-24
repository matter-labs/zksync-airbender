import GKRCompiler.Arithmetic

namespace Airbender.Compiler
set_option warningAsError true

/-- A formal polynomial identity over the base field remains an identity in
any target ring through a ring homomorphism, including at extension challenges. -/
def evaluateHom [CommRing F] [CommRing R] (hom : F →+* R) (values : Fin n → R)
    (polynomial : Polynomial n F) : R :=
  (polynomial.map (fun term => hom term.1 * monomialValue values term.2)).sum

@[simp] theorem evaluateHom_cons [CommRing F] [CommRing R] (hom : F →+* R) (values : Fin n → R)
    (term : F × Monomial n) (rest : Polynomial n F) :
    evaluateHom hom values (term :: rest) = hom term.1 * monomialValue values term.2 + evaluateHom hom values rest := by
  simp [evaluateHom]

@[simp] theorem evaluateHom_constant [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin n → R) (scalar : F) : evaluateHom hom values (constant scalar) = hom scalar := by
  simp [evaluateHom, constant, monomialValue]

@[simp] theorem evaluateHom_atom [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin n → R) (wire : Fin n) : evaluateHom hom values (atom wire) = values wire := by
  simp [evaluateHom, atom, monomialValue]

@[simp] theorem evaluateHom_add [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin n → R) (left right : Polynomial n F) :
    evaluateHom hom values (add left right) = evaluateHom hom values left + evaluateHom hom values right := by
  simp [evaluateHom, add, List.map_append, List.sum_append]

@[simp] theorem evaluateHom_negate [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin n → R) (polynomial : Polynomial n F) :
    evaluateHom hom values (negate polynomial) = -evaluateHom hom values polynomial := by
  induction polynomial with
  | nil => simp [negate, evaluateHom]
  | cons term rest proof =>
      change hom (-term.1) * monomialValue values term.2 + evaluateHom hom values (negate rest) = _
      rw [map_neg, proof, evaluateHom_cons]
      ring

@[simp] theorem evaluateHom_multiply [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin n → R) (left right : Polynomial n F) :
    evaluateHom hom values (multiply left right) = evaluateHom hom values left * evaluateHom hom values right := by
  have row (term : F × Monomial n) (items : Polynomial n F) :
      evaluateHom hom values (items.map (fun other => (term.1 * other.1, term.2 ++ other.2))) =
        hom term.1 * monomialValue values term.2 * evaluateHom hom values items := by
    induction items with
    | nil => simp [evaluateHom]
    | cons other rest proof =>
        simp only [List.map_cons, evaluateHom_cons, map_mul, monomial_append, proof]
        ring
  induction left with
  | nil => simp [multiply, evaluateHom]
  | cons term rest proof =>
      change evaluateHom hom values
        (add (right.map (fun other => (term.1 * other.1, term.2 ++ other.2))) (multiply rest right)) = _
      rw [evaluateHom_add, row, proof, evaluateHom_cons]
      ring

theorem evaluateHom_insertTerm [CommRing F] [DecidableEq F] [CommRing R] (hom : F →+* R)
    (values : Fin n → R) (term : F × Monomial n) (polynomial : Polynomial n F) :
    evaluateHom hom values (insertTerm term polynomial) =
      hom term.1 * monomialValue values term.2 + evaluateHom hom values polynomial := by
  induction polynomial with
  | nil => simp [insertTerm, evaluateHom]; split_ifs <;> simp_all
  | cons head tail proof =>
      simp only [insertTerm]
      split_ifs with zero same sumZero earlier
      · simp [zero, evaluateHom]
      · simp only [evaluateHom_cons]
        rw [← same]
        rw [← add_assoc, ← add_mul, ← map_add, sumZero, map_zero, zero_mul, zero_add]
      · simp only [evaluateHom_cons, map_add]
        rw [← same]
        ring
      · rfl
      · simp only [evaluateHom_cons, proof]
        ring

theorem evaluateHom_normalize [CommRing F] [DecidableEq F] [CommRing R] (hom : F →+* R)
    (values : Fin n → R) (polynomial : Polynomial n F) :
    evaluateHom hom values (normalize polynomial) = evaluateHom hom values polynomial := by
  induction polynomial with
  | nil => rfl
  | cons term rest proof =>
      simp only [normalize, List.foldr_cons, evaluateHom_insertTerm, evaluateHom_cons]
      have ordered : monomialValue values
          (term.2.insertionSort (fun left right => left.val ≤ right.val)) = monomialValue values term.2 :=
        List.Perm.prod_eq ((List.perm_insertionSort _ _).map values)
      rw [ordered]
      exact congrArg (fun value => hom term.1 * monomialValue values term.2 + value) proof

theorem equal_hom_sound [CommRing F] [DecidableEq F] [CommRing R]
    {left right : Polynomial n F} (checked : equal left right = true)
    (hom : F →+* R) (values : Fin n → R) :
    evaluateHom hom values left = evaluateHom hom values right := by
  have same : normalize left = normalize right := of_decide_eq_true checked
  rw [← evaluateHom_normalize hom values left, ← evaluateHom_normalize hom values right, same]

theorem monomialValue_hom [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin n → F) (monomial : Monomial n) :
    monomialValue (hom ∘ values) monomial = hom (monomialValue values monomial) := by
  induction monomial with
  | nil => simp [monomialValue]
  | cons wire rest proof =>
      simpa only [monomialValue, List.map_cons, List.prod_cons, Function.comp_apply, map_mul] using
        congrArg (hom (values wire) * ·) proof

theorem evaluateHom_at_hom [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin n → F) (polynomial : Polynomial n F) :
    evaluateHom hom (hom ∘ values) polynomial = hom (evaluate values polynomial) := by
  induction polynomial with
  | nil => simp [evaluateHom]
  | cons term rest proof =>
      rw [evaluateHom_cons, evaluate_cons, monomialValue_hom, proof, map_add, map_mul]

theorem evaluateHom_rename [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin m → R) (placement : Fin n → Fin m) (polynomial : Polynomial n F) :
    evaluateHom hom values (rename placement polynomial) = evaluateHom hom (values ∘ placement) polynomial := by
  simp [evaluateHom, rename, monomialValue, List.map_map, Function.comp_def]

theorem combination_hom_zero [CommRing F] [CommRing R] (hom : F →+* R)
    {relations : List (Polynomial n F)} {values : Fin n → R}
    (holds : ∀ relation ∈ relations, evaluateHom hom values relation = 0)
    (terms : Combination relations) : evaluateHom hom values (combination relations terms) = 0 := by
  induction terms with
  | nil => rfl
  | cons term rest proof =>
      simp only [combination, List.foldr_cons, evaluateHom_add, evaluateHom_multiply,
        holds _ (List.get_mem _ _), mul_zero, zero_add]
      exact proof

def Expression.valueHom [CommRing F] [CommRing R] (hom : F →+* R) (values : Fin n → R) : Expression n F → R
  | .constant scalar => hom scalar
  | .atom wire => values wire
  | .add left right => left.valueHom hom values + right.valueHom hom values
  | .mul left right => left.valueHom hom values * right.valueHom hom values

theorem Expression.polynomial_valueHom [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin n → R) (expression : Expression n F) :
    evaluateHom hom values expression.polynomial = expression.valueHom hom values := by
  induction expression with
  | constant scalar => exact evaluateHom_constant _ _ _
  | atom wire => exact evaluateHom_atom _ _ _
  | add left right leftProof rightProof => simpa only [polynomial, valueHom, evaluateHom_add] using congrArg₂ (· + ·) leftProof rightProof
  | mul left right leftProof rightProof => simpa only [polynomial, valueHom, evaluateHom_multiply] using congrArg₂ (· * ·) leftProof rightProof

end Airbender.Compiler
