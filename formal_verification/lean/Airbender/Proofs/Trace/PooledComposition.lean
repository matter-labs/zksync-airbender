import Airbender.Proofs.Trace.PooledExecution
import Airbender.Proofs.Trace.PooledCode

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

set_option backward.isDefEq.respectTransparency false in
/-- The shared composition rule consumes actual earlier pooled transfers,
    preserves public decoding and proves original Sail retirement. This slice
    dispatches the register-writing families; memory/control rows follow. -/
theorem pooled_register_step {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    (registers : ∀ index, Cell.register index ∈ cells)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (loads : NoDiscardedLoads program)
    {row : Row p PooledFamily} (member : row ∈ trace.rows)
    (registerFamily : row.family = .addSub ∨ row.family = .mulDiv ∨ row.family = .shiftBinop)
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
    | wordMemory | jumpBranchSlt | subwordMemory => simp at registerFamily

end Airbender.Trace.Proofs
