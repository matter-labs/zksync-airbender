module
public import Human.Circuits.Bigint.Execution
public import Human.Trace.Delegation.RVExecution
public import Human.ISA.Delegations

@[expose] public section

/-! The delegate link of the bigint worker: each bigint row is one `.delegate` call of our RV32 spec
    (`RV.Delegation.bigint`, via `RV.Delegation.effect`). There is no span: one call is the whole 256-bit operation.
    RAM cells are RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`
    (`RV.State.delegationRAM`); no pointer is required to be at or above `ROM_END`. -/

namespace Airbender.Bigint.Native
open Trace

/-- One bigint row inside the RV history `events` (from `before` to `after`): its accesses run as one call, from
    `start` to `finish` (the split of `Delegation.RVCallExecution`), and the spec's bigint call from `start` has an
    effect whose application is `finish`, up to the spec's PC advance. RAM cells include READ-WRITE ACCESS TO THE
    SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def RVCallLink (cells : List Cell) (events : List MemoryAccess) (before after : RV.State)
    (row : Delegation.Row p) : Prop :=
  ∃ earlier current newer start finish,
    events = newer ++ current ++ earlier ∧
    current.Perm (row.memorySteps.map transferEvent) ∧
    RVHistory cells earlier before start ∧
    RVHistory cells current start finish ∧
    RVHistory cells newer finish after ∧
    ∃ s', (RV.Delegation.effect .bigint (start.getReg 10) (start.getReg 11) (start.getReg 12)
        start.delegationRAM).bind start.applyEffect = some s' ∧
      RV.Same s' (finish.setPC (start.pc + 4))

/-- The delegate link of a pool: one actual RV history of all the pool's accesses, in native timestamp order from
    `before`, in which every bigint row is one spec bigint call (`RVCallLink`). RAM cells include READ-WRITE ACCESS
    TO THE SHADOW RAM BELOW `ROM_END`. -/
def RVCalls (data : Delegation.MemoryData p) (before : RV.State) (cells : List Cell) : Prop :=
  ∃ (events : List MemoryAccess) (after : RV.State),
    events.Perm (data.steps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    RVHistory cells events before after ∧
    ∀ row ∈ data.rows, row.family = .bigint → RVCallLink cells events before after row

end Airbender.Bigint.Native
