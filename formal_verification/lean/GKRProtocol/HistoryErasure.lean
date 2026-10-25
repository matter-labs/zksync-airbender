import GKRProtocol.OriginalInputs

namespace Airbender.Compiler
set_option warningAsError true
variable {F : Type}

def eraseCoordinates (coordinates : List (Fin n)) (values : Fin n → F) [Zero F] (index : Fin n) : F :=
  if coordinates.contains index then 0 else values index

def erasurePolynomials [CommRing F] (coordinates : List (Fin n)) (index : Fin n) : Polynomial n F :=
  if coordinates.contains index then constant 0 else atom index

theorem erasurePolynomials_value [CommRing F] (coordinates : List (Fin n)) (values : Fin n → F) (index : Fin n) :
    evaluate values (erasurePolynomials coordinates index) = eraseCoordinates coordinates values index := by
  unfold erasurePolynomials eraseCoordinates
  split <;> simp only [evaluate_constant, evaluate_atom]

theorem eraseCoordinates_frame [Zero F] (coordinates : List (Fin n)) (values : Fin n → F)
    (index : Fin n) (outside : index ∉ coordinates) : eraseCoordinates coordinates values index = values index := by
  simp [eraseCoordinates, outside]

theorem eraseCoordinates_at [Zero F] (coordinates : List (Fin n)) (values : Fin n → F)
    (index : Fin n) (inside : index ∈ coordinates) : eraseCoordinates coordinates values index = 0 := by
  simp [eraseCoordinates, inside]

def erasureUntouched (coordinates : List (Fin n)) (polynomial : Polynomial n F) : Bool :=
  polynomial.all (fun term => term.2.all (fun wire => !coordinates.contains wire))

theorem erasure_evaluate_same [CommRing F] (coordinates : List (Fin n)) (polynomial : Polynomial n F)
    (untouched : erasureUntouched coordinates polynomial = true) (values : Fin n → F) :
    evaluate (eraseCoordinates coordinates values) polynomial = evaluate values polynomial := by
  unfold evaluate
  congr 1
  apply List.map_congr_left
  intro term member
  congr 1
  unfold monomialValue
  congr 1
  apply List.map_congr_left
  intro wire included
  apply eraseCoordinates_frame
  have outside := List.all_eq_true.mp (List.all_eq_true.mp untouched term member) wire included
  simpa using outside

def erasureCheck [CommRing F] [DecidableEq F] (coordinates : List (Fin n)) (relations : List (Polynomial n F)) : Bool :=
  relations.all (fun polynomial => erasureUntouched coordinates polynomial ||
    (equal (substitute (erasurePolynomials coordinates) polynomial) [] ||
      equal (substitute (erasurePolynomials coordinates) polynomial) polynomial))

/-- Erasing source history fields either leaves each source equation unchanged
or makes it zero. The finite check supplies no replacement source equations. -/
theorem erasure_satisfies [CommRing F] [DecidableEq F] (coordinates : List (Fin n))
    (relations : List (Polynomial n F)) (checked : erasureCheck coordinates relations = true)
    (values : Fin n → F) (holds : Satisfies relations values) :
    Satisfies relations (eraseCoordinates coordinates values) := by
  intro polynomial member
  have clause := List.all_eq_true.mp checked polynomial member
  have interpretation : (fun index => evaluate values (erasurePolynomials coordinates index)) =
      eraseCoordinates coordinates values := funext (erasurePolynomials_value coordinates values)
  have substitution := evaluate_substitute values (erasurePolynomials coordinates) polynomial
  rw [interpretation] at substitution
  have cases : erasureUntouched coordinates polynomial = true ∨
      (equal (substitute (erasurePolynomials coordinates) polynomial) [] = true ∨
        equal (substitute (erasurePolynomials coordinates) polynomial) polynomial = true) := by
    simpa only [Bool.or_eq_true] using clause
  rcases cases with untouched | zero | same
  · exact (erasure_evaluate_same coordinates polynomial untouched values).trans (holds polynomial member)
  · exact substitution.symm.trans ((equal_sound zero values).trans rfl)
  · exact substitution.symm.trans ((equal_sound same values).trans (holds polynomial member))

theorem memoryField_erasure (field : Source.MemoryField) (placement : Source.MemoryPlacement n)
    (coordinates : List (Fin n))
    (checked : equal (substitute (erasurePolynomials coordinates) (field.polynomial placement))
      (field.polynomial placement) = true) (values : Fin n → Source.BaseField) :
    field.value (placement.project (eraseCoordinates coordinates values)) = field.value (placement.project values) := by
  rw [← field.polynomial_value, ← field.polynomial_value]
  have interpretation : (fun index => evaluate values (erasurePolynomials coordinates index)) =
      eraseCoordinates coordinates values := funext (erasurePolynomials_value coordinates values)
  have result := evaluate_substitute values (erasurePolynomials coordinates) (field.polynomial placement)
  rw [interpretation] at result
  exact result.symm.trans (equal_sound checked values)

end Airbender.Compiler
