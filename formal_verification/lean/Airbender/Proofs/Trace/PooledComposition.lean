import Airbender.Proofs.Trace.PooledExecution
import Airbender.Proofs.Trace.PooledCode
import Airbender.Proofs.Trace.PooledMemory
import Airbender.Proofs.Trace.PooledSubword
import Airbender.Review.Trace.PooledExecution
import Airbender.Proofs.VerifierBoundary

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

set_option backward.isDefEq.respectTransparency false in
/-- The shared composition rule consumes actual earlier pooled transfers,
    preserves public decoding and proves original Sail retirement. This slice
    covers all six pooled families through the same register/RAM history. -/
theorem pooled_row_step {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (memoryConfiguration : FlatMemoryConfiguration initial)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (loads : NoDiscardedLoads program)
    (terminal : trace.terminal.word.Bounded)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0)
    {row : Row p PooledFamily} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    StepWith pooledDecoderFields instructionClause program (retiredState before row.start.word.toBitVec)
      (retiredState after row.finish.word.toBitVec) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := pooled_source_after_history (by omega) inverse accepted clocks image
    programImage present (code entry present) native past
  have fetched := native_query_pc_word limbSize query
  change row.start.word = Word.ofBitVec entry.pc at fetched
  have position : row.start.word.toBitVec = entry.pc := by rw [fetched, Word.ofBitVec_roundtrip]
  have pc : run (SailRV32.Functions.get_arch_pc ()) (retiredState before row.start.word.toBitVec) =
      .ok entry.pc (retiredState before row.start.word.toBitVec) := by
    simpa only [position] using retired_state_pc before row.start.word.toBitVec
  refine ⟨entry, present, entry_source_retired_state source _, pc, ?_⟩
  cases row with
  | mk kind w =>
    cases kind with
    | addSub =>
      exact pooled_arithmetic_execution .sail hp inverse accepted clocks image wordSetup subwordSetup
        registers programImage decoded member present family query (fun _ => loads entry present) past history
    | mulDiv =>
      exact pooled_muldiv_execution hp inverse accepted clocks image wordSetup subwordSetup
        programImage decoded member present family query history
    | shiftBinop =>
      exact pooled_shift_execution hp inverse accepted clocks image
        programImage decoded member present family query history
    | jumpBranchSlt =>
      exact pooled_control_execution hp inverse accepted clocks image wordSetup subwordSetup
        programImage decoded (fun entry present => (code entry present).2) terminal
        member present family query past history isa configuration
    | wordMemory =>
      exact pooled_word_execution hp inverse accepted clocks image wordSetup subwordSetup
        aligned ordinary memoryConfiguration programImage decoded member present family query native past history
    | subwordMemory =>
      exact pooled_subword_execution hp inverse accepted clocks image wordSetup subwordSetup
        aligned ordinary memoryConfiguration programImage decoded member present family query native past history

set_option backward.isDefEq.respectTransparency false in
/-- One actual Sail execution for the entire pooled witness. The initialized
    chronological history supplies every family's reads and input ranges. -/
theorem pooled_trace_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} {initial : State} {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledInputs trace initial cells program)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program) :
    Realizes (PooledStep program) trace initial cells := by
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
  have execution := compose_native_rows initialRead
    (fun row member {before after events} native past current =>
      pooled_row_step hp inverse accepted inputs.clocks inputs.image inputs.wordSetup inputs.subwordSetup
        inputs.registers inputs.aligned inputs.ordinary inputs.configuration programImage decoded inputs.code
        inputs.loads (VerifierBoundary.Proofs.trace_terminal_bound limbSize accepted inputs.verifierBoundary) inputs.configuration.isa
        ⟨inputs.configuration.privilege, inputs.landingPadDisabled⟩ member native past current)
    rows trace.terminal (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  exact native_trace_postconditions clockSize inverse accepted inputs.clocks
    inputs.image inputs.distinct initialRead consistent chain nativeHistory matchedState execution

end Airbender.Trace.Proofs
