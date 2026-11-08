module
public import Human.Trace.Workers.Blake2Round.Call
public import Human.Trace.Workers.Blake2Round.RVCompression
public import Human.Helpers.Delegation.RVBoundaryMemory
public import Human.Trace.Delegation.RVExecution
public import Human.Helpers.Delegation.NativeWindows
public import Human.ISA.DelegationRuns

@[expose] public section

/-! RV siblings of the extended-BLAKE call, boundary-call and window contracts (`Call.lean`, `BoundaryCall.lean`,
    `Windows.lean`): the public state is an `RV.State`; RAM cells are RAM at any address, INCLUDING READ-WRITE ACCESS
    TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`); no pointer is required to be at or above `ROM_END`. -/

namespace Airbender.Blake2Round
open Trace

/-- The calls of one complete extended-BLAKE request: seven round delegations when the reduced-round flag is set,
    ten otherwise. -/
abbrev rvCalls (flags : Fin 8) : List RV.DelegationKind :=
  List.replicate (if flags.val % 2 = 1 then 7 else 10) .blakeRound

/-- RV sibling of `CallInputs`: one uninterrupted extended-BLAKE request span from a public `RV.State`. -/
structure RVCallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (initial : RV.State)
    (cells : List Cell) (flags : Fin 8) : Prop where
  memory : Delegation.RVMemoryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  controlStart : (Cell.register 12).readRV initial = some (BitVec.ofNat 32 ((8 + flags.val) * 65536))
  calls : data.rows.length = if flags.val % 2 = 1 then 7 else 10

/-- RV sibling of `NativeCallInputs`: the complete extended-BLAKE caller ABI at a native boundary, retaining seed
    clocks. -/
structure RVNativeCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : RV.State) (cells : List Cell) (flags : Fin 8) : Prop where
  memory : Delegation.RVBoundaryMemoryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  controlStart : (Cell.register 12).readRV initial = some (BitVec.ofNat 32 ((8 + flags.val) * 65536))
  calls : data.rows.length = if flags.val % 2 = 1 then 7 else 10

/-- RV sibling of `WindowInputs`: the first complete seven/ten-round span within one initialized ten-position
    controller, from a retained native boundary `RV.State`. -/
structure RVWindowInputs [Fact p.Prime] (data : Delegation.MemoryData p) (before : RV.State)
    (cells : List Cell) (flags : Fin 8) (lower upper : Nat) : Prop where
  memory : Delegation.RVBoundaryMemoryInputs data before cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  controlStart : (Cell.register 12).readRV before = some (BitVec.ofNat 32 ((8 + flags.val) * 65536))
  prefixEmpty : data.prefixRows lower = []
  roundsBound : data.rows.length ≤ 10
  calls : (data.windowRows lower upper).length = if flags.val % 2 = 1 then 7 else 10

/-- RV sibling of `HashSpan.Result` for `.blakeRound flags`: the complete compression reference on actual initial/final
    RV RAM, the same final state executing every native access (`RVTraceMapping`), and the delegate link: the final
    state IS the spec's run of the request's round delegations (`RV.calls (rvCalls flags)`, `RV.Delegation.blakeRound`)
    from `before`, up to the spec's PC advance. -/
def RVSpanResult [Fact p.Prime] (flags : Fin 8) (workers : Delegation.MemoryData p)
    (before after : RV.State) (cells : List Cell) : Prop :=
  ∃ (statePointer messagePointer : BitVec 32) (input : Compression.State)
    (message : Vector Arithmetic.Word 16) (output : Compression.State),
    Compression.RVWordMapping before after statePointer messagePointer input output message ∧
      Delegation.RVTraceMapping workers before after cells ∧
      output = Compression.run flags input message ∧
      ∃ s', RV.calls (rvCalls flags) before = some s' ∧
        RV.Same s' (after.setPC (before.pc + BitVec.ofNat 32 (4 * (rvCalls flags).length)))

end Airbender.Blake2Round
