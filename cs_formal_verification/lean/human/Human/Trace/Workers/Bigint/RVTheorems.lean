module
public import Human.Trace.Workers.Bigint.RVCall
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

-- The statements proven in slop/Slop/Final/Trace/Workers/Bigint/RVTheorems.lean (checked by verify.sh). The public starting point is an `RV.State`; RAM cells are RAM at any address, INCLUDING
-- READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`): no pointer is required to be at or
-- above `ROM_END`. The claim also states the delegate link: every bigint row is one spec bigint call
-- (`RV.Delegation.bigint`), its post-state the spec's effect applied to its pre-state.

namespace Airbender.Bigint.Native

/-- All seven selected bigint operations act on the values realized by actual
    RV port reads/writes (`RVMemoryExecution`), and every bigint row, the no-opcode row included, is one spec bigint
    call (`RVCalls`): from the call's pre-state the spec's effect exists (its pointer, alignment and control guards
    hold) and applying it gives the call's post-state, up to the spec's PC advance. Other delegation families may share
    the history. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def RVOperationExecutionClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {before : RV.State} {cells : List Trace.Cell} (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.RVMemoryInputs data before cells) (aligned : ∀ cell ∈ cells, cell.Aligned) (table : data.setup.bigint = setupTable),
    Delegation.RVMemoryExecution data before cells ∧
      (∀ row ∈ data.rows, row.family = .bigint → ArithmeticEffects row.assignment) ∧
      RVCalls data before cells

end Airbender.Bigint.Native
