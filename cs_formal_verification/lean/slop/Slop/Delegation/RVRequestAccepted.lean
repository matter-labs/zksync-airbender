module
public import Human.Helpers.Delegation.RVRequestTrace

@[expose] public section

/-! The worker-only part of the request checks, as the delegation memory acceptance its proofs take. -/

namespace Airbender.Delegation.Caller

theorem RVRequestAccepted.workers {p : Nat} [Fact p.Prime] {data : RVRequestTrace p}
    (accepted : RVRequestAccepted data) : MemoryAccepted data.workers :=
  ⟨accepted.workerConstraints, accepted.workerMemory⟩

end Airbender.Delegation.Caller
