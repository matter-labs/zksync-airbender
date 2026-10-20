import Slop.Blake2Round.Soundness.Outputs

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem column_mapping {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (mapping : Mixing.WordMapping input output w) (call : Fin 4) :
    Blake2G.WordMapping (callInput 0 call input.state input.message)
      (columnOutputs w call) (columnGAssignment call w) := by
  rw [mapping.state, mapping.message]
  fin_cases call <;> constructor
  all_goals simp [callInput, callConstants, Specs.BLAKE3.roundConstants,
    Blake2G.State.Proofs.project, Preparation.words, Variables.preparedState,
    Variables.scheduledMessage, columnOutputs, gOutput, columnGAssignment,
    columnGBase, Blake2G.Proofs.assemble, Fin.getElem_fin]

end Airbender.Blake2Round.Proofs
