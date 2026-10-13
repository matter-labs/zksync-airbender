import Airbender.Review.Trace.UnifiedReduced.PreparedHashWindows

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Public literal preparation followed by an uninterrupted extended-BLAKE caller
    suffix. Matching derives its selectors, control sequence and round masks. -/
structure PreparedRoundInputs [Fact p.Prime] (data : RequestTrace p) (before : State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry)
    (flags : Fin 8) (lower : Nat) : Prop where
  /-- Original public CSR decoding and the initialized native clock. -/
  publicProgram : RequestInputs data before ca
  /-- Original decoding constructs the ordinary literal registry. -/
  ordinaryProgram : Mixed.programImage before oa = some program
  /-- Actual public cell reads construct the architectural seed. -/
  initialization : initialImage before cells = some data.machine.initialMemory
  /-- Physical cells are initialized once. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- Tracked words retain the public alignment profile. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Unified tables use this public memory. -/
  setup : data.machine.rom = Setup.table before
  /-- Original modeled worker tables. -/
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  /-- The worker pool uses the extended-round family. -/
  family : ∀ row ∈ data.workers.rows, row.family = .blakeRound
  /-- Public LUI registry and the existing empty worker-prefix scope. -/
  preparation : ControlPreparation data program lower 12 (hashPreparation (.blakeRound flags))
  /-- The existing controller has ten positions. -/
  roundsBound : data.workers.rows.length ≤ 10
  /-- Public suffix duration; matching derives an uninterrupted caller region. -/
  duration : (timeOfPair data.machine.terminal.timestamp).value = lower + 4 * data.workers.rows.length

/-- Complete first compression inside that prepared caller suffix. Later rounds
    may remain outside the selected window within the same ten-position controller. -/
structure PreparedRoundWindowInputs [Fact p.Prime] (data : RequestTrace p) (before : State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry)
    (flags : Fin 8) (lower upper : Nat) : Prop extends PreparedRoundInputs data before ca oa cells program flags lower where
  /-- Seven or ten calls, according to the public flags. -/
  calls : (data.workers.windowRows lower upper).length = (Delegation.Caller.HashSpan.blakeRound flags).callCount
  /-- Public selected-span duration. -/
  spanDuration : upper = lower + 4 * (Delegation.Caller.HashSpan.blakeRound flags).callCount
  /-- The selected final cut lies within the native path. -/
  beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value

end Airbender.UnifiedReduced.Caller
