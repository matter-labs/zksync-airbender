import GKRProtocol.HistoryErasure
import GKRCompiler.Reduction

namespace Airbender.Compiler
set_option warningAsError true
variable {F R : Type}

/-- History is observable only on executing rows. On padding rows choose zero
history, leaving every other source coordinate unchanged. -/
def inactiveHistory [Zero F] [DecidableEq F] (coordinates : List (Fin n))
    (execute : F) (values : Fin n → F) : Fin n → F :=
  if execute = 0 then eraseCoordinates coordinates values else values

theorem inactiveHistory_active [Zero F] [DecidableEq F] (coordinates : List (Fin n))
    (execute : F) (active : execute ≠ 0) (values : Fin n → F) :
    inactiveHistory coordinates execute values = values := by
  simp [inactiveHistory, active]

theorem inactiveHistory_frame [Zero F] [DecidableEq F] (coordinates : List (Fin n))
    (execute : F) (values : Fin n → F) (index : Fin n) (outside : index ∉ coordinates) :
    inactiveHistory coordinates execute values index = values index := by
  unfold inactiveHistory
  split
  · exact eraseCoordinates_frame coordinates values index outside
  · rfl

theorem inactiveHistory_satisfies [CommRing F] [DecidableEq F] (coordinates : List (Fin n))
    (relations : List (Polynomial n F)) (checked : erasureCheck coordinates relations = true)
    (execute : F) (values : Fin n → F) (holds : Satisfies relations values) :
    Satisfies relations (inactiveHistory coordinates execute values) := by
  unfold inactiveHistory
  split
  · exact erasure_satisfies coordinates relations checked values holds
  · exact holds

/-- This holds for every fingerprint and challenge, including zero. It does
not use a sampled product equality to infer equality of memory multisets. -/
theorem inactiveHistory_maskProduct [CommRing F] [DecidableEq F] [CommRing R]
    (hom : F →+* R) (coordinates : List (Fin n)) (execute : F)
    (values : Fin n → F) (effect : (Fin n → F) → R) :
    maskProduct (hom execute) (effect (inactiveHistory coordinates execute values)) =
      maskProduct (hom execute) (effect values) := by
  by_cases inactive : execute = 0
  · simp only [inactive, map_zero, maskProduct_inactive]
  · rw [inactiveHistory_active coordinates execute inactive values]

end Airbender.Compiler
