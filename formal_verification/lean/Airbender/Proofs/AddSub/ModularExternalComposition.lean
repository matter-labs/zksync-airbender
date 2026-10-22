import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.AddSub.ModularExternalExecution
import Airbender.Proofs.Trace.PooledOracleComposition

namespace Airbender.AddSub.Modular.External.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Trace.Proofs
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
set_option warningAsError true

set_option backward.isDefEq.respectTransparency false in
theorem trace_execution
    (hp : 536870912 ≤ babyBearModulus) (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} {initial : State} {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledInputs trace initial cells program External.decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program)
    {stream : List (BitVec 32)} (ports : External.StreamPorts trace stream) :
    External.Realizes stream program trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < babyBearModulus := by dsimp [timestampBase]; omega
  have limbSize : limbBase < babyBearModulus := by dsimp [limbBase]; omega
  obtain ⟨timestamp, initialBound⟩ := inputs.initialPC
  obtain ⟨addresses, programImage⟩ := inputs.programImage
  have initialRead := initial_state_pc limbSize initialBound
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    pooled_native_history clockSize inverse accepted inputs.clocks inputs.image
      inputs.distinct inputs.aligned programImage decoded
  have chain := ordered_row_boundaries clockSize inverse accepted inputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection clockSize inverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have indices : ∀ current ∈ rows, External.readIndex trace current =
      (rows.filter fun earlier => External.isRead earlier && decide (earlier.clock < current.clock)).length :=
    fun current _ => (permutation.filter _).length_eq.symm
  have execution := ExternalStream.Proofs.compose_rows_with_clause External.isRead (External.readIndex trace)
    initialRead
    (fun row member {before after events} native past current =>
      row_step hp inverse accepted inputs.clocks inputs.image inputs.wordSetup inputs.subwordSetup
        inputs.registers inputs.aligned inputs.ordinary inputs.configuration programImage decoded inputs.code
        inputs.loads (VerifierBoundary.Proofs.trace_terminal_bound limbSize accepted inputs.verifierBoundary) inputs.configuration.isa
        ⟨inputs.configuration.privilege, inputs.landingPadDisabled⟩ ports member native past current)
    rows ordered indices trace.terminal (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  have count : (rows.filter External.isRead).length = External.readCount trace :=
    (permutation.filter External.isRead).length_eq
  rw [count] at execution
  let final := ExternalStream.Proofs.finalState rows nativeAfter trace.terminal.word.toBitVec
  have pc : run (SailRV32.Functions.get_arch_pc ()) final =
      .ok trace.terminal.word.toBitVec final := by
    cases rows with
    | nil =>
      have same : trace.terminal = trace.initial := by simpa using chain
      rw [same]
      exact sail_history_pc_read nativeHistory initialRead
    | cons _ _ => exact retired_state_pc nativeAfter trace.terminal.word.toBitVec
  have realized : SailStateMatches cells history final := by
    cases rows with
    | nil => exact matchedState
    | cons _ _ =>
      exact matches_control
        (matches_control matchedState .nextPC (.inr rfl) trace.terminal.word.toBitVec)
        .PC (.inl rfl) trace.terminal.word.toBitVec
  exact ⟨final, execution, pc, terminal_sail_reads clockSize inverse accepted inputs.clocks
    inputs.image inputs.distinct consistent realized⟩

theorem native_trace_execution
    (hp : 536870912 ≤ babyBearModulus) (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} {before : State} {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs trace before cells program External.decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program)
    {stream : List (BitVec 32)} (ports : External.StreamPorts trace stream) :
    External.Realizes stream program trace before cells (ROMView.token before) := by
  have clockSize : 2 * timestampBase + 4 < babyBearModulus := by dsimp [timestampBase]; omega
  have size : 4 < babyBearModulus := by omega
  have clocks := ROMView.native_clocks size inputs.seed inputs.initialBoundary
  obtain ⟨after, execution, pc, terminal⟩ := trace_execution hp inverse
    (PooledROMView.execution_boundary size inputs)
    (PooledROMView.accepted clockSize inverse before accepted clocks inputs.seed)
    (PooledROMView.decoded before decoded) (NonDeterminism.Pooled.Proofs.view_ports before ports)
  change ExecutionTrace stream program (before, 0)
    (after, NonDeterminism.Pooled.readCount (PooledROMView.data before trace)) at execution
  rw [NonDeterminism.Pooled.Proofs.view_count] at execution
  refine ⟨after, execution, pc, ?_⟩
  intro sink member
  have lifted := terminal (ROMView.token before sink) (List.mem_map_of_mem member)
  simpa only [ROMView.token_address, id_eq] using lifted

end Airbender.AddSub.Modular.External.Proofs
