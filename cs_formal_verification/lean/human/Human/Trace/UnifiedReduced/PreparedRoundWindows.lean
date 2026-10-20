import Human.Trace.UnifiedReduced.PreparedHashWindows
import Human.Helpers.UnifiedReduced.WindowSchedule

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
  /-- Public LUI registry and the worker-free final preparation cycle. -/
  preparation : ControlPreparation data program lower 12 (hashPreparation (.blakeRound flags))
  /-- This extended-round scope still starts before any worker in its pool. -/
  prefixEmpty : data.workers.prefixRows lower = []
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

/-- One prepared extended-BLAKE controller region; earlier workers remain outside it. -/
structure RoundRegion where
  flags : Fin 8
  lower : Nat
  upper : Nat

/-- Local protocol shape used to derive round masks from raw joint matching.
    No mask, control read, empty worker prefix or global ten-row cap is supplied. -/
structure RoundRegionInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (region : RoundRegion) : Prop where
  /-- Only workers inside this controller region use extended BLAKE. -/
  family : ∀ row ∈ data.workers.windowRows region.lower region.upper, row.family = .blakeRound
  /-- Actual public LUI prepares this controller's flags and first round. -/
  preparation : ControlPreparation data program region.lower 12 (hashPreparation (.blakeRound region.flags))
  /-- This controller region has at most ten positions. -/
  roundsBound : (data.workers.windowRows region.lower region.upper).length ≤ 10
  /-- Public duration; matching derives that every included machine row is a caller. -/
  duration : region.upper = region.lower + 4 * (data.workers.windowRows region.lower region.upper).length
  /-- Instruction-boundary cuts. -/
  aligned : region.lower % 4 = 0 ∧ region.upper % 4 = 0
  /-- The region remains inside the native path. -/
  beforeTerminal : region.upper ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Shared public memory/program inputs and prepared regions covering every round
    worker. Masks follow from these regions; other worker families remain in history. -/
structure PreparedProtocolInputs [Fact p.Prime] (data : RequestTrace p) (before : State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry)
    (regions : List RoundRegion) : Prop where
  /-- Original public CSR decoding and the initial native clock. -/
  publicProgram : RequestInputs data before ca
  /-- Original Sail decoding constructs the ordinary instruction registry. -/
  ordinaryProgram : Mixed.programImage before oa = some program
  /-- Successful public cell reads construct the joint seed. -/
  initialization : initialImage before cells = some data.machine.initialMemory
  /-- One initialized token per physical cell. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- Public tracked-RAM alignment. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Unified modeled setup uses the same public image. -/
  setup : data.machine.rom = Setup.table before
  /-- Existing modeled worker tables and Keccak controller. -/
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  /-- Each controller restart has its own public preparation and local shape. -/
  scopes : ∀ region ∈ regions, RoundRegionInputs data program region
  /-- Every actual extended-round worker belongs to an admitted prepared region.
      This is an explicit protocol-shape boundary, not general acceptance coverage. -/
  coverage : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ region ∈ regions, row ∈ data.workers.windowRows region.lower region.upper

/-- A complete selected G, extended-BLAKE or Keccak span. Global masks are derived
    through `PreparedProtocolInputs`; each span retains its public protocol ABI. -/
structure PreparedProtocolWindowInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (window : HashWindow) : Prop where
  /-- The selected complete span has one worker family. -/
  family : ∀ row ∈ data.workers.windowRows window.lower window.upper, row.family = window.span.family
  /-- Public literal preparation; only its final cycle is worker-free. -/
  preparation : ControlPreparation data program window.lower window.span.controlRegister (hashPreparation window.span)
  /-- Existing complete-reference call count. -/
  calls : (data.workers.windowRows window.lower window.upper).length = window.span.callCount
  /-- Public duration; native matching derives its caller selectors. -/
  duration : window.upper = window.lower + 4 * window.span.callCount
  /-- The final cut lies inside the native path. -/
  beforeTerminal : window.upper ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Public code selects the complete span's callers. Native matching derives
    worker family and count; controller coverage remains in the shared inputs. -/
structure ProgramProtocolWindowInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (window : HashWindow) : Prop where
  /-- Public addresses exclude ordinary code and identify full CSR families. -/
  region : ProgramCallerRegion data program window.span.family window.lower window.upper
  /-- The specified public literal prepares the actual control. -/
  preparation : ControlPreparation data program window.lower window.span.controlRegister (hashPreparation window.span)
  /-- Public cuts cover the existing reference's number of four-tick calls. -/
  duration : window.upper = window.lower + 4 * window.span.callCount
  /-- The selected final cut stays in the native path. -/
  beforeTerminal : window.upper ≤ (timeOfPair data.machine.terminal.timestamp).value

end Airbender.UnifiedReduced.Caller
