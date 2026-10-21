import Airbender.Proofs.Blake2Round.FrameOutputs
import Airbender.Proofs.Blake2Round.Reference
import Airbender.Review.Circuits.Blake2Round.Mixing
import Airbender.Proofs.Blake2G.FrameMapping

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Native layout binds the stable column-frame inputs to the reviewed round
    input. The G mapping itself is supplied by Frame.mapping. -/
theorem native_column_frame_input {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (mapping : Mixing.WordMapping input output w) (call : Fin 4) :
    (columnFrame call w).input = callInput 0 call input.state input.message := by
  rw [mapping.state, mapping.message]
  fin_cases call
  all_goals simp [Blake2G.Proofs.Frame.input, columnFrame, NativeLayout.column,
    NativeLayout.columnInputs, NativeLayout.Layout.read, NativeLayout.Location.read,
    callInput, callConstants, Specs.BLAKE3.roundConstants, Blake2G.State.Proofs.project,
    Preparation.words, Variables.preparedState, Variables.scheduledMessage, Fin.getElem_fin]

theorem native_column_mapping {p : Nat} {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (mapping : Mixing.WordMapping input output w) (call : Fin 4) :
    Blake2G.WordMapping (callInput 0 call input.state input.message)
      (columnOutputs w call) (nativeColumnAssignment call w) := by
  have certificate := (columnFrame call w).mapping
  rw [native_column_frame_input mapping call] at certificate
  exact certificate

/-- Diagonal lanes are routed through stable column outputs. Physical storage
    is read by NativeLayout; it is absent from the round's semantic proof. -/
theorem native_diagonal_frame_input {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (mapping : Mixing.WordMapping input output w) (call : Fin 4) :
    (diagonalFrame call w).input =
      callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message := by
  rw [mapping.message]
  fin_cases call
  all_goals simp [Blake2G.Proofs.Frame.input, diagonalFrame, diagonalIncoming,
    NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read,
    callInput, callConstants, Specs.BLAKE3.roundConstants, phaseUpdate, callUpdate,
    Blake2G.State.Proofs.project, Blake2G.State.Proofs.update, Preparation.words,
    Variables.scheduledMessage, columnOutputs, gOutput, nativeColumnAssignment,
    Fin.getElem_fin]
  all_goals constructor <;> rfl

theorem native_diagonal_mapping {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    {input : Mixing.Input} {output : Mixing.Output}
    (mapping : Mixing.WordMapping input output w) (call : Fin 4) :
    Blake2G.WordMapping
      (callInput 1 call (phaseUpdate 0 input.state (columnOutputs w)) input.message)
      (diagonalOutputs w call) (nativeDiagonalAssignment call w) := by
  have certificate := (diagonalFrame call w).mapping
  rw [native_diagonal_frame_input mapping call] at certificate
  exact certificate

end Airbender.Blake2Round.Proofs
