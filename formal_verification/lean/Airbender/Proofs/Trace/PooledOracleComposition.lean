import Airbender.Proofs.Trace.PooledOracleExecution
import Airbender.Proofs.Trace.PooledROMView
import Airbender.Proofs.Trace.ExternalComposition

namespace Airbender.Trace.NonDeterminism.Pooled.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace.Proofs

theorem view_clock {p : Nat} [Fact p.Prime] (initial : State) (row : Row p PooledFamily) :
    (PooledROMView.row initial row).clock = row.clock := by
  change (timeOfPair (PooledROMView.row initial row).start.timestamp).value =
    (timeOfPair row.start.timestamp).value
  rw [PooledROMView.row_start]

theorem view_read {p : Nat} [Fact p.Prime] (initial : State) (row : Row p PooledFamily) :
    Pooled.isRead (PooledROMView.row initial row) = Pooled.isRead row := by
  cases row with
  | mk family w =>
    cases family <;> first | rfl | (dsimp only [PooledROMView.row]; split <;> rfl)

theorem view_response {p : Nat} [Fact p.Prime] (initial : State) (row : Row p PooledFamily)
    (read : Pooled.isRead row = true) :
    Pooled.response (PooledROMView.row initial row) = Pooled.response row := by
  cases row with
  | mk family w =>
    cases family <;> first | rfl | cases read

theorem view_index {p : Nat} [Fact p.Prime] (initial : State) (trace : PooledTrace p)
    (row : Row p PooledFamily) :
    Pooled.readIndex (PooledROMView.data initial trace) (PooledROMView.row initial row) =
      Pooled.readIndex trace row := by
  simp only [Pooled.readIndex, ExternalStream.index, PooledROMView.data,
    List.filter_map, List.length_map, Function.comp_def, view_read, view_clock]

theorem view_count {p : Nat} [Fact p.Prime] (initial : State) (trace : PooledTrace p) :
    Pooled.readCount (PooledROMView.data initial trace) = Pooled.readCount trace := by
  simp only [Pooled.readCount, ExternalStream.count, PooledROMView.data,
    List.filter_map, List.length_map, Function.comp_def, view_read]

theorem view_ports {p : Nat} [Fact p.Prime] (initial : State) {trace : PooledTrace p}
    {stream : List (BitVec 32)} (ports : Pooled.StreamPorts trace stream) :
    Pooled.StreamPorts (PooledROMView.data initial trace) stream := by
  intro physical member read
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
  have selected : Pooled.isRead row = true := (view_read initial row).symm.trans read
  change stream[Pooled.readIndex (PooledROMView.data initial trace) (PooledROMView.row initial row)]? =
    some (Pooled.response (PooledROMView.row initial row))
  rw [view_index, view_response initial row selected]
  exact ports row present selected

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

set_option backward.isDefEq.respectTransparency false in
theorem trace_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} {initial : State} {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledInputs trace initial cells program Pooled.decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program)
    {stream : List (BitVec 32)} (ports : Pooled.StreamPorts trace stream) :
    Pooled.Realizes stream program trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
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
  have indices : ∀ current ∈ rows, Pooled.readIndex trace current =
      (rows.filter fun earlier => Pooled.isRead earlier && decide (earlier.clock < current.clock)).length :=
    fun current _ => (permutation.filter _).length_eq.symm
  have execution := ExternalStream.Proofs.compose_rows Pooled.isRead (Pooled.readIndex trace)
    initialRead
    (fun row member {before after events} native past current =>
      row_step hp inverse accepted inputs.clocks inputs.image inputs.wordSetup inputs.subwordSetup
        inputs.registers inputs.aligned inputs.ordinary inputs.configuration programImage decoded inputs.code
        inputs.loads (VerifierBoundary.Proofs.trace_terminal_bound limbSize accepted inputs.verifierBoundary) inputs.configuration.isa
        ⟨inputs.configuration.privilege, inputs.landingPadDisabled⟩ ports member native past current)
    rows ordered indices trace.terminal (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  have count : (rows.filter Pooled.isRead).length = Pooled.readCount trace :=
    (permutation.filter Pooled.isRead).length_eq
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

theorem native_trace_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} {before : State} {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs trace before cells program Pooled.decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program)
    {stream : List (BitVec 32)} (ports : Pooled.StreamPorts trace stream) :
    Pooled.Realizes stream program trace before cells (ROMView.token before) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have size : 4 < p := by omega
  have clocks := ROMView.native_clocks size inputs.seed inputs.initialBoundary
  obtain ⟨after, execution, pc, terminal⟩ := trace_execution hp inverse
    (PooledROMView.execution_boundary size inputs)
    (PooledROMView.accepted clockSize inverse before accepted clocks inputs.seed)
    (PooledROMView.decoded before decoded) (view_ports before ports)
  rw [view_count] at execution
  refine ⟨after, execution, pc, ?_⟩
  intro sink member
  have lifted := terminal (ROMView.token before sink) (List.mem_map_of_mem member)
  simpa only [ROMView.token_address, id_eq] using lifted

end Airbender.Trace.NonDeterminism.Pooled.Proofs
