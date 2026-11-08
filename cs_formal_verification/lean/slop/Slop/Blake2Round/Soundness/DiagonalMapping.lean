module
public import Slop.Blake2Round.Soundness.Outputs

@[expose] public section

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem diagonal_mapping {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (mapping : Mixing.WordMapping input output w) (call : Fin 4) :
    callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message =
      (diagonalTrace call.val w).input := by
  rw [mapping.message, diagonalTrace_input]
  fin_cases call
  all_goals simp [callInput, callConstants, Specs.BLAKE3.roundConstants,
    phaseUpdate, callUpdate, Blake2G.State.Proofs.project, Blake2G.State.Proofs.update,
    Preparation.words, Variables.scheduledMessage, columnOutputs, Fin.getElem_fin]

end Airbender.Blake2Round.Proofs
