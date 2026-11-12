module
public import Human.Trace.UnifiedReduced.RVPreparedHashWindows
public import Human.Trace.UnifiedReduced.PreparedRoundWindows

@[expose] public section

/-! Unified caller window contracts: states are
    `RV.State`s, cells are read by `Cell.readRV` and executed by `RVHistory`, programs are RV program tables. A RAM cell
    is RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Public literal preparation followed by an uninterrupted extended-BLAKE caller
    suffix. Matching derives its selectors, control sequence and round masks. -/
structure RVPreparedRoundInputs [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.RVProgramEntry)
    (flags : Fin 8) (lower : Nat) : Prop where
  /-- Original public CSR decoding and the initialized native clock. -/
  publicProgram : RVRequestInputs data before ca
  /-- Original decoding constructs the ordinary literal registry. -/
  ordinaryProgram : rvProgramImageWith UnifiedReduced.rvDecoderFields before oa = some program
  /-- Actual public cell reads construct the architectural seed. -/
  initialization : initialImageRV before cells = some data.machine.initialMemory
  /-- Physical cells are initialized once. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- Tracked words retain the public alignment profile. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Unified tables use this public memory. -/
  setup : data.machine.rom = Setup.tableRV before
  /-- Original modeled worker tables. -/
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  /-- The worker pool uses the extended-round family. -/
  family : ∀ row ∈ data.workers.rows, row.family = .blakeRound
  /-- Public LUI registry and the worker-free final preparation cycle. -/
  preparation : RVControlPreparation data program lower 12 (hashPreparation (.blakeRound flags))
  /-- This extended-round scope still starts before any worker in its pool. -/
  prefixEmpty : data.workers.prefixRows lower = []
  /-- The existing controller has ten positions. -/
  roundsBound : data.workers.rows.length ≤ 10
  /-- Public suffix duration; matching derives an uninterrupted caller region. -/
  duration : (timeOfPair data.machine.terminal.timestamp).value = lower + 4 * data.workers.rows.length

/-- Complete first compression inside that prepared caller suffix. Later rounds
    may remain outside the selected window within the same ten-position controller. -/
structure RVPreparedRoundWindowInputs [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.RVProgramEntry)
    (flags : Fin 8) (lower upper : Nat) : Prop extends RVPreparedRoundInputs data before ca oa cells program flags lower where
  /-- Seven or ten calls, according to the public flags. -/
  calls : (data.workers.windowRows lower upper).length = (Delegation.Caller.HashSpan.blakeRound flags).callCount
  /-- Public selected-span duration. -/
  spanDuration : upper = lower + 4 * (Delegation.Caller.HashSpan.blakeRound flags).callCount
  /-- The selected final cut lies within the native path. -/
  beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Local protocol shape used to derive round masks from raw joint matching.
    No mask, control read, empty worker prefix or global ten-row cap is supplied. -/
structure RVRoundRegionInputs [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) (region : RoundRegion) : Prop where
  /-- Only workers inside this controller region use extended BLAKE. -/
  family : ∀ row ∈ data.workers.windowRows region.lower region.upper, row.family = .blakeRound
  /-- Actual public LUI prepares this controller's flags and first round. -/
  preparation : RVControlPreparation data program region.lower 12 (hashPreparation (.blakeRound region.flags))
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
structure RVPreparedProtocolInputs [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.RVProgramEntry)
    (regions : List RoundRegion) : Prop where
  /-- Original public CSR decoding and the initial native clock. -/
  publicProgram : RVRequestInputs data before ca
  /-- The RV ROM image and `RV.decode` construct the ordinary instruction registry. -/
  ordinaryProgram : rvProgramImageWith UnifiedReduced.rvDecoderFields before oa = some program
  /-- Successful public cell reads construct the joint seed. -/
  initialization : initialImageRV before cells = some data.machine.initialMemory
  /-- One initialized token per physical cell. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- Public tracked-RAM alignment. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Unified modeled setup uses the same public image. -/
  setup : data.machine.rom = Setup.tableRV before
  /-- Existing modeled worker tables and Keccak controller. -/
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  /-- Each controller restart has its own public preparation and local shape. -/
  scopes : ∀ region ∈ regions, RVRoundRegionInputs data program region
  /-- Every actual extended-round worker belongs to an admitted prepared region.
      This is an explicit protocol-shape boundary, not general acceptance coverage. -/
  coverage : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ region ∈ regions, row ∈ data.workers.windowRows region.lower region.upper

/-- A complete selected G, extended-BLAKE or Keccak span. Global masks are derived
    through `RVPreparedProtocolInputs`; each span retains its public protocol ABI. -/
structure RVPreparedProtocolWindowInputs [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) (window : HashWindow) : Prop where
  /-- The selected complete span has one worker family. -/
  family : ∀ row ∈ data.workers.windowRows window.lower window.upper, row.family = window.span.family
  /-- Public literal preparation; only its final cycle is worker-free. -/
  preparation : RVControlPreparation data program window.lower window.span.controlRegister (hashPreparation window.span)
  /-- Existing complete-reference call count. -/
  calls : (data.workers.windowRows window.lower window.upper).length = window.span.callCount
  /-- Public duration; native matching derives its caller selectors. -/
  duration : window.upper = window.lower + 4 * window.span.callCount
  /-- The final cut lies inside the native path. -/
  beforeTerminal : window.upper ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Public code selects the complete span's callers. Native matching derives
    worker family and count; controller coverage remains in the shared inputs. -/
structure RVProgramProtocolWindowInputs [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) (window : HashWindow) : Prop where
  /-- Public addresses exclude ordinary code and identify full CSR families. -/
  region : RVProgramCallerRegion data program window.span.family window.lower window.upper
  /-- The specified public literal prepares the actual control. -/
  preparation : RVControlPreparation data program window.lower window.span.controlRegister (hashPreparation window.span)
  /-- Public cuts cover the existing reference's number of four-tick calls. -/
  duration : window.upper = window.lower + 4 * window.span.callCount
  /-- The selected final cut stays in the native path. -/
  beforeTerminal : window.upper ≤ (timeOfPair data.machine.terminal.timestamp).value

end Airbender.UnifiedReduced.Caller
