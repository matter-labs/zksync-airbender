import GKRCompiler.Arithmetic

namespace Airbender.Compiler
set_option warningAsError true

/-- A field of an independently reconstructed source request and its actual
lowered counterpart. The witness may use only the actual relation bank. -/
structure Agreement (relations : List (Polynomial n F)) where
  source : Polynomial n F
  lowered : Polynomial n F
  witness : Combination relations

def Agreement.check [CommRing F] [DecidableEq F] {relations : List (Polynomial n F)}
    (agreement : Agreement relations) : Bool :=
  equal agreement.source (add agreement.lowered (combination relations agreement.witness))

theorem Agreement.sound [CommRing F] [DecidableEq F] {relations : List (Polynomial n F)}
    {agreement : Agreement relations} (checked : agreement.check = true)
    {values : Fin n → F} (holds : Satisfies relations values) :
    evaluate values agreement.source = evaluate values agreement.lowered := by
  have result := equal_sound checked values
  rw [evaluate_add, combination_zero holds, add_zero] at result
  exact result

/-- Componentwise agreement preserves the entire encoded tuple, including
zero padding and the table selector. Equal lengths are part of the type. -/
theorem tuple_agreement [CommRing F] [DecidableEq F] {relations : List (Polynomial n F)}
    (fields : Fin width → Agreement relations)
    (checked : ∀ index, (fields index).check = true)
    {values : Fin n → F} (holds : Satisfies relations values) :
    (fun index => evaluate values (fields index).source) =
      (fun index => evaluate values (fields index).lowered) := by
  funext index
  exact Agreement.sound (checked index) holds

end Airbender.Compiler
