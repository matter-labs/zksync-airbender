module
public import Proven.UnifiedReduced.Proth120.RowWitness
public import Human.Circuits.UnifiedReduced.Proth120Clock
public import Proven.Constraints

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

theorem modular_result_satisfiable : ModularResultSatisfiableClaim :=
  ⟨Witness.setup, Witness.assignment .fma, .fma, Witness.holds _, Witness.selected _,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, rfl⟩

theorem clock_advance_satisfiable : ClockAdvanceSatisfiableClaim :=
  ⟨Witness.setup, Witness.assignment .fma, Verification.holds_append (Witness.holds _) (Witness.clocks _),
   ⟨by decide, by decide⟩, rfl⟩

theorem row_soundness_satisfiable : RowSoundnessSatisfiableClaim :=
  ⟨_, _, _, _, _, Witness.fma_inputs⟩

end Airbender.UnifiedReduced.Proth120
