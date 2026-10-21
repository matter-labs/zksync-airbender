import Airbender.Proofs.Blake2Round.Reference

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- The four disjoint calls overwrite all sixteen lanes. Native writeback
    checks therefore need not expand the preceding phase's circuit layout. -/
theorem phase_update_initial_irrelevant (phase : Fin 2)
    (first second : Vector Arithmetic.Word 16) (output : Fin 4 → Blake2G.Words) :
    phaseUpdate phase first output = phaseUpdate phase second output := by
  have lane (i : Fin 16) : (phaseUpdate phase first output)[i] =
      (phaseUpdate phase second output)[i] := by
    fin_cases phase <;> fin_cases i
    all_goals simp [phaseUpdate, callUpdate, callConstants, Specs.BLAKE3.roundConstants,
      Blake2G.State.Proofs.update]
  apply Vector.ext
  intro i hi
  exact lane ⟨i, hi⟩

end Airbender.Blake2Round.Proofs
