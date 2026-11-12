module
public import Proven.Bigint.RVCallStep
public import Proven.Delegation.RVRowCalls
public import Proven.Delegation.RVExecution
public import Human.Trace.Workers.Bigint.RVTheorems

@[expose] public section

/-! RV twin of `NativeExecution.native_operation_execution`, with the delegate link: native bigint rows inside actual
    RV memory execution (RAM cells include read-write shadow RAM below `ROM_END`), each row one spec bigint call. -/

namespace Airbender.Bigint.Native.Proofs
open Trace
set_option warningAsError true

theorem rv_operation_execution {data : Delegation.MemoryData babyBearModulus}
    {before : RV.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.RVMemoryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (table : data.setup.bigint = setupTable) :
    Delegation.RVMemoryExecution data before cells ∧
      (∀ row ∈ data.rows, row.family = .bigint → ArithmeticEffects row.assignment) ∧
      RVCalls data before cells := by
  have hp : 2 * timestampBase + 4 < babyBearModulus := by norm_num [timestampBase, babyBearModulus]
  have seed := inputs.toRVBoundaryInputs.toSeed
  refine ⟨Delegation.Proofs.rv_native_memory_execution hp accepted inputs aligned, ?_, ?_⟩
  · intro row member family
    have holds := accepted.constraints row member
    rcases row with ⟨kind, w⟩
    change kind = .bigint at family
    subst kind
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints data.setup.bigint) at holds
    rw [table] at holds
    exact arithmetic_effects (Verification.holds_of_sublist holds
      (List.sublist_append_left (importedConstraints setupTable) importedConstraintsTimestampLookups))
  · obtain ⟨_, events, after, _, permutation, order, history, _⟩ :=
      Delegation.Proofs.rv_native_history hp accepted inputs.toRVBoundaryInputs aligned
    refine ⟨events, after, permutation, order, history, ?_⟩
    intro row member family
    rcases row with ⟨kind, w⟩
    change kind = .bigint at family
    subst kind
    obtain ⟨earlier, current, newer, start, finish, split, grouped, past, call, later⟩ :=
      Delegation.Proofs.rv_row_call hp accepted seed permutation order history member
    exact ⟨earlier, current, newer, start, finish, split, grouped, past, call, later,
      Bigint.Proofs.rv_bigint_call accepted seed table aligned member call grouped⟩

end Airbender.Bigint.Native.Proofs
