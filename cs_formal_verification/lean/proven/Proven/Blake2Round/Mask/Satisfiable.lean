module
public import Proven.Blake2Round.Mask.Native
public import Proven.NonVacuous.Blake2RoundSpan.Seed
public import Proven.NonVacuous.Blake2RoundSpan.Ports
public import Proven.NonVacuous.Blake2RoundSpan.Row

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic

/-- The existing verified first round supplies a native row assignment. -/
theorem satisfiable : SatisfiableClaim := by
  let w : Nat → ZMod babyBearModulus :=
    (NonVacuous.Blake2RoundSpan.inputAt NonVacuous.Blake2RoundSpan.seed 1 (⟨0, by decide⟩ : Fin 10)).assignment
  have valid := NonVacuous.Blake2RoundSpan.valid NonVacuous.Blake2RoundSpan.seed_inv
    (by decide) (by decide) (by decide)
  have clocks := NonVacuous.Blake2RoundSpan.holds (p := babyBearModulus) rfl valid
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable) :=
    Verification.holds_of_sublist clocks (List.sublist_append_left _ _)
  have reads : ∀ i : Fin 43, (readWord w i).Bounded := by
    intro i
    have observed := NonVacuous.Blake2RoundSpan.read
      NonVacuous.Blake2RoundSpan.seed_inv (by decide) i.val i.isLt
    have bounded := NonVacuous.Blake2RoundSpan.seed_inv.words _
      (NonVacuous.Blake2RoundSpan.cellAt_mem i.isLt)
    rw [← observed] at bounded
    dsimp only [readWord, w]
    convert bounded using 1
  exact ⟨inputOf w, outputOf w, w, native_assumptions reads, core, native_mapping core⟩

end Airbender.Blake2Round.Mask.Proofs
