module
public import Human.Trace.Workers.Keccak.Permutation
public import Human.Helpers.Delegation.RVBoundaryMemory
public import Human.Trace.Delegation.RVExecution
public import Human.ISA.DelegationRuns
public import Human.Helpers.Delegation.NativeWindows
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector

@[expose] public section

/-! RV siblings of the Keccak special5 call, boundary-call, window and permutation contracts (`Call.lean`,
    `BoundaryCall.lean`, `Windows.lean`, `Permutation.lean`): the public state is an `RV.State`; RAM cells are RAM at
    any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`); no pointer
    is required to be at or above `ROM_END`. -/

namespace Airbender.Keccak
open Trace

/-- The calls of one complete special5 request: 649 Keccak special5 delegations (`RV.Delegation.keccakSpecial5`). -/
abbrev rvCalls : List RV.DelegationKind := List.replicate 649 .keccak

/-- RV sibling of `CallInputs`: one uninterrupted special5 request span from a public `RV.State`. -/
structure RVCallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (initial : RV.State)
    (cells : List Cell) : Prop where
  memory : Delegation.RVMemoryInputs data initial cells
  controlCell : Cell.register 10 ∈ cells
  controlStart : (Cell.register 10).readRV initial = some 0
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  calls : data.rows.length = 649

/-- RV sibling of `NativeCallInputs`: the complete special5 ABI at a native boundary, retaining seed clocks. -/
structure RVNativeCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : RV.State) (cells : List Cell) : Prop where
  memory : Delegation.RVBoundaryMemoryInputs data initial cells
  controlStart : (Cell.register 10).readRV initial = some 0
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  calls : data.rows.length = 649

/-- RV sibling of `WindowInputs`: the first complete special5 span in a native worker pool. -/
structure RVWindowInputs [Fact p.Prime] (data : Delegation.MemoryData p) (before : RV.State)
    (cells : List Cell) (lower upper : Nat) : Prop where
  memory : Delegation.RVBoundaryMemoryInputs data before cells
  tables : data.setup = Delegation.modeledSetup Controller.rows
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  controlStart : (Cell.register 10).readRV before = some 0
  prefixEmpty : data.prefixRows lower = []
  calls : (data.windowRows lower upper).length = 649

/-- RV sibling of `Permutation.LanesAt`: the 25 permutation lanes are RV RAM reads (`Cell.readRV`), each lane its
    low and high 32-bit words, at Clean's column-major lane offsets in the row-major block. -/
def Permutation.RVLanesAt (state : RV.State) (pointer : BitVec 32) (lanes : Vector Nat 25) : Prop :=
  ∀ lane : Fin 25, ∃ low high : BitVec 32,
    (Cell.ram (pointer + BitVec.ofNat 32 (laneOffset lane))).readRV state = some low ∧
    (Cell.ram (pointer + BitVec.ofNat 32 (laneOffset lane) + 4)).readRV state = some high ∧
    lanes[lane] = low.toNat + 2 ^ 32 * high.toNat ∧ lanes[lane] < 2 ^ 64

/-- RV sibling of `Permutation.WordMapping`: public x11 and the initial/final permutation block, read from RV states. -/
structure Permutation.RVWordMapping (initial after : RV.State) (pointer : BitVec 32)
    (input output : Vector Nat 25) : Prop where
  pointerRead : (Cell.register 11).readRV initial = some pointer
  inputLanes : RVLanesAt initial pointer input
  outputLanes : RVLanesAt after pointer output

/-- RV sibling of `HashSpan.Result` for `.keccak`: Clean's Keccak permutation on actual initial/final RV RAM, the same
    final state executing every native access (`RVTraceMapping`), and the delegate link: the final state IS the spec's
    run of the 649 special5 delegations (`RV.calls rvCalls`, `RV.Delegation.keccakSpecial5`) from `before`, up to the
    spec's PC advance. -/
def RVSpanResult [Fact p.Prime] (workers : Delegation.MemoryData p) (before after : RV.State)
    (cells : List Cell) : Prop :=
  ∃ (pointer : BitVec 32) (input output : Vector Nat 25),
    Permutation.RVWordMapping before after pointer input output ∧
      Delegation.RVTraceMapping workers before after cells ∧
      output = Specs.Keccak256.keccakPermutation input ∧
      ∃ s', RV.calls rvCalls before = some s' ∧
        RV.Same s' (after.setPC (before.pc + BitVec.ofNat 32 (4 * rvCalls.length)))

end Airbender.Keccak
