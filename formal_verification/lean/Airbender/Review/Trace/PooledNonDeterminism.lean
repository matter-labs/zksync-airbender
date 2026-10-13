import Airbender.Review.Trace.NonDeterminism
import Airbender.Review.Helpers.Decoder.PooledExternalInput

namespace Airbender.Trace.NonDeterminism.Pooled
variable {p : Nat} [Fact p.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- One mixed step, using public Sail fetch/decoding and the shared custom CSR
    clause. Standard instructions execute unchanged Sail; only external reads
    advance the independent stream position. -/
abbrev Step := NonDeterminism.StepWith decoderFields .sail

/-- Finite mixed execution with one fixed external stream for the whole run. -/
abbrev ExecutionTrace (stream : List (BitVec 32)) (program : List PooledProgramEntry) :=
  Relation.ReflTransGen (Step stream program)

/-- A whole mixed execution reaches the native final PC and tracked cell values,
    consuming exactly `readCount trace` words from the fixed external stream.
    `view` interprets native ROM shadow tokens using public bytes for boot traces.
    This is the proved conclusion; it adds no read, range or result assumptions. -/
def Realizes (stream : List (BitVec 32)) (program : List PooledProgramEntry)
    (trace : PooledTrace p) (initial : Reference.RiscV.Sail.State) (cells : List Cell)
    (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ after, ExecutionTrace stream program (initial, 0) (after, readCount trace) ∧
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after =
      .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (view sink).word.toBitVec after

end Airbender.Trace.NonDeterminism.Pooled
