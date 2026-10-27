import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Memory.Native
import Human.Trace.Families.AddSub.Execution
import Human.ISA.Sail.View

/-! DRAFT (B2 pilot): the ADD/SUB + word-memory trace claims stated against runs of our RV32 spec (`RV.run`).
Not proven yet; not in `test/Checks/Claims.lean`. `ExecutionBoundary`/`NativeBootBoundary` still carry
`configuration : Configured initial`; it is to leave the bundles. The Sail-profile claim has no RV counterpart:
our spec is the Airbender profile (a load into x0 only advances the PC). -/

namespace Airbender.Trace

/-- The value of a tracked cell in an `RV.State`: a register as instructions read it, a RAM word little-endian. -/
def Cell.rvValue (s : RV.State) : Cell → RV.Word
  | .register index => s.getReg index
  | .ram address    => RV.read s.mem address 4

/-- An accepted trace is a run of our spec from the public initial state (for any input) to a state whose PC and
tracked cells are the trace's terminal ones (`view` reinterprets native tokens, as in `Realizes`). -/
def RVRealizes {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (trace : Data p Kind)
    (initial : Reference.RiscV.Sail.State) (cells : List Cell) (stream : List RV.Word)
    (tokenView : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ n after, RV.run n (Airbender.view initial stream) = some after ∧ after.pc = trace.terminal.word.toBitVec ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.rvValue after = (tokenView sink).word.toBitVec

def RVSoundnessClaim : Prop :=
  ∀ {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State} {cells : List Cell} {program : List ProgramEntry} (inputs : ExecutionBoundary trace before cells program) (accepted : Accepted trace) (decoded : Decoded trace program) (stream : List RV.Word),
    RVRealizes trace before cells stream

def RVNativeBootSoundnessClaim : Prop :=
  ∀ {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State} {cells : List Cell} {program : List ProgramEntry} (inputs : NativeBootBoundary trace before cells program) (accepted : Accepted trace) (decoded : Decoded trace program) (stream : List RV.Word),
    RVRealizes trace before cells stream (ROMView.token before)

end Airbender.Trace
