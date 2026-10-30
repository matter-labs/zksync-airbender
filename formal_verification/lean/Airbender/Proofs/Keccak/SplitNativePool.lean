import Airbender.Proofs.Keccak.SplitNativeSetup
import Airbender.Proofs.Keccak.SplitMemoryOrder

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- Exact native RAM matching and the retained tables give the complete split
pool's logical history. No controller-semantic premise is an input. -/
theorem fixed_memory_history
    (hp : FieldCapacity.ClockNoWrap babyBearModulus timestampBase)
    {data : RequestTrace babyBearModulus} (binding : RequestClockBinding data)
    (accepted : MemoryAccepted data.workers) (tables : data.workers.setup = fixedSetup)
    (initialClocks : ∀ token ∈ data.workers.initial, (timeOfPair token.time).Bounded) :
    (data.workers.initial ++ data.workers.steps.map Prod.snd).Perm
        (data.workers.terminal ++ data.workers.steps.map Prod.fst) ∧
      (∀ edge ∈ data.workers.steps, edge.1.address = edge.2.address) ∧
      (∀ edge ∈ data.workers.steps,
        (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value) := by
  have control : ControlSetupFacts data.workers.setup := by
    rw [tables]
    exact fixed_control_setup_facts
  exact ordered_memory_history hp binding accepted control initialClocks

end Airbender.Keccak.Split.Native.Proofs
