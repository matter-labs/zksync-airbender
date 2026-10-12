import Airbender.Review.Delegation.RequestEffects
import Airbender.Proofs.Delegation.RequestTrace
import Airbender.Review.Bigint.Theorems
import Airbender.Proofs.Blake2G.Claims
import Airbender.Proofs.Blake2Round.Claims
import Airbender.Proofs.Keccak.Claims

namespace Airbender.Delegation.Caller.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true

theorem request_operation_effects
    {data : RequestTrace babyBearModulus} {before : State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RequestAccepted data) (inputs : RequestOperationInputs data before addresses cells) :
    RequestOperationEffects data before cells := by
  have execution := request_memory_execution (by decide) (by decide) (by decide)
    accepted inputs.publicState
  have initialized : MemoryInputs data.workers before cells :=
    ⟨inputs.publicState.initialization, inputs.publicState.distinct, execution.requests.clockRoom⟩
  have operation : OperationInputs data.workers before cells Keccak.Controller.rows := {
    publicState := initialized
    tables := inputs.tables
    rounds := inputs.rounds
    keccakActive := by
      intro row present family
      have active := accepted.workerActive row present
      rw [Delegation.Row.columns, family] at active
      change row.assignment 0 = 1 at active ⊢
      exact active }
  have words := Delegation.operation_memory_soundness (by decide) (by decide) accepted.workers operation
  have bigint := Bigint.Native.operation_execution accepted.workers initialized inputs.publicState.aligned
    (by rw [inputs.tables]; rfl)
  have blakeG := Blake2G.Native.operation_execution (by decide) (by decide)
    accepted.workers operation inputs.publicState.aligned
  have blakeRound := Blake2Round.Native.operation_execution (by decide) (by decide)
    accepted.workers operation inputs.publicState.aligned
  have keccak := Keccak.Native.operation_execution (by decide) (by decide)
    accepted.workers operation inputs.publicState.aligned
  refine ⟨execution, words.2, ?_⟩
  intro row present
  cases family : row.family
  all_goals simp only [WorkerEffect, family]
  · exact bigint.2 row present family
  · exact blakeG.2 row present family
  · exact blakeRound.2 row present family
  · exact keccak.2 row present family

end Airbender.Delegation.Caller.Proofs
