module
public import Human.Trace.Workers.Blake2G.WorkVector
public import Human.Trace.Workers.Blake2Round.RVCompression
public import Human.Helpers.Delegation.RVBoundaryMemory
public import Human.Trace.Delegation.RVExecution
public import Human.Helpers.Delegation.NativeWindows
public import Human.ISA.DelegationRuns

@[expose] public section

/-! G call, boundary-call, window and work-vector contracts: the public state is an `RV.State`; RAM cells are RAM at any address, INCLUDING
    READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`); no pointer is required to be at or
    above `ROM_END`. -/

namespace Airbender.Blake2G
open Trace

/-- The calls of one complete G-only request: 56 `G` delegations in the reduced (7-round) mode, 80 otherwise. -/
abbrev rvCalls (reduced : Bool) : List RV.DelegationKind :=
  List.replicate (callCount reduced) .blakeG

/-- One uninterrupted G-only request span from a public `RV.State`. -/
structure RVCallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (initial : RV.State)
    (cells : List Cell) (reduced : Bool) : Prop where
  memory : Delegation.RVMemoryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  controlStart : (Cell.register 12).readRV initial = some (if reduced then 128 else 0)
  calls : data.rows.length = callCount reduced

/-- The complete G caller ABI at a native boundary, retaining seed clocks. -/
structure RVNativeCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : RV.State) (cells : List Cell) (reduced : Bool) : Prop where
  memory : Delegation.RVBoundaryMemoryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  controlStart : (Cell.register 12).readRV initial = some (if reduced then 128 else 0)
  calls : data.rows.length = callCount reduced

/-- One complete G-worker span selected after whole preceding spans. -/
structure RVWindowInputs [Fact p.Prime] (data : Delegation.MemoryData p) (before : RV.State)
    (cells : List Cell) (reduced : Bool) (lower upper : Nat) : Prop where
  memory : Delegation.RVMemoryInputs data before cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  controlStart : (Cell.register 12).readRV before = some (if reduced then 128 else 0)
  prefixComplete : (data.prefixRows lower).length % callCount reduced = 0
  calls : (data.windowRows lower upper).length = callCount reduced

/-- Actual public pointers, initialized input/message words, and result words
    read (`Cell.readRV`) from the same final `RV.State` exposed by `Delegation.RVTraceMapping`. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
structure WorkVector.RVWordMapping (initial after : RV.State) (statePointer messagePointer : BitVec 32)
    (input message output : Vector Arithmetic.Word 16) : Prop where
  pointers : (Cell.register 10).readRV initial = some statePointer ∧
    (Cell.register 11).readRV initial = some messagePointer
  inputWords : Blake2Round.Compression.RVWordsAt initial statePointer 0 input
  messageWords : Blake2Round.Compression.RVWordsAt initial messagePointer 0 message
  outputWords : Blake2Round.Compression.RVWordsAt after statePointer 0 output
  messageUnchanged : Blake2Round.Compression.RVWordsAt after messagePointer 0 message

/-- Result of a `.blakeG reduced` span: the complete G work-vector reference on actual initial/final
    RV RAM, the same final state executing every native access (`RVTraceMapping`), and the delegate link: the final
    state IS the spec's run of the request's `G` delegations (`RV.calls (rvCalls reduced)`, `RV.Delegation.blakeG`)
    from `before`, up to the spec's PC advance. -/
def RVSpanResult [Fact p.Prime] (reduced : Bool) (workers : Delegation.MemoryData p)
    (before after : RV.State) (cells : List Cell) : Prop :=
  ∃ (statePointer messagePointer : BitVec 32) (input message output : Vector Arithmetic.Word 16),
    WorkVector.RVWordMapping before after statePointer messagePointer input message output ∧
      Delegation.RVTraceMapping workers before after cells ∧
      output.map Arithmetic.Word.value = WorkVector.run reduced input message ∧
      ∃ s', RV.calls (rvCalls reduced) before = some s' ∧
        RV.Same s' (after.setPC (before.pc + BitVec.ofNat 32 (4 * (rvCalls reduced).length)))

end Airbender.Blake2G
