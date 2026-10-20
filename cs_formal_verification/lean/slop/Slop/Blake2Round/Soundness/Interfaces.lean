import Slop.Blake2Round.Soundness.Outputs

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem column_interface {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (interface : Mixing.InterfaceAssumptions input output w) (call : Fin 4) :
    Blake2G.InterfaceAssumptions (callInput 0 call input.state input.message)
      (columnOutputs w call) (columnGAssignment call w) := by
  fin_cases call <;> constructor
  all_goals simp only [callInput, callConstants, Specs.BLAKE3.roundConstants,
    Blake2G.State.Proofs.project]
  all_goals first
    | exact (interface.additionInputs 0).1 | exact (interface.additionInputs 1).1
    | exact (interface.additionInputs 2).1 | exact (interface.additionInputs 3).1
    | exact (interface.additionInputs 0).2 | exact (interface.additionInputs 1).2
    | exact (interface.additionInputs 2).2 | exact (interface.additionInputs 3).2
    | exact interface.messages 0 | exact interface.messages 1
    | exact interface.messages 2 | exact interface.messages 3
    | exact interface.messages 4 | exact interface.messages 5
    | exact interface.messages 6 | exact interface.messages 7

theorem diagonal_messages {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (interface : Mixing.InterfaceAssumptions input output w) (call : Fin 4) :
    (callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message).mx.Bounded ∧
      (callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message).my.Bounded := by
  fin_cases call <;> constructor
  all_goals simp only [callInput, callConstants, Specs.BLAKE3.roundConstants]
  all_goals first
    | exact interface.messages 8 | exact interface.messages 9
    | exact interface.messages 10 | exact interface.messages 11
    | exact interface.messages 12 | exact interface.messages 13
    | exact interface.messages 14 | exact interface.messages 15

end Airbender.Blake2Round.Proofs
