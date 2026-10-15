import Airbender.Proofs.UnifiedReduced.BigintCalls

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Every successful bigint caller in any actual accepted shared history executes
    the full independent project reference and retires Sail's PC advance.
    The F02 valid-command restriction is temporary, while pointers, operands,
    writes and the frame follow from constraints and initialized matching.
    This upgrades the bigint callers of the existing mixed-cycle certificate;
    hash-call reference retirement and total worker accounting remain separate. -/
theorem bigint_call_soundness
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells) (commands : BigintCommands data)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState) :
    ∀ row ∈ data.callers, (request row.assignment).csr = Delegation.Requests.csr .bigint →
      BigintCallCycle data initial finalState cells events row :=
  fun _ member kind => Proofs.bigint_call_cycle_at accepted inputs code commands
    (Proofs.mixed_memory_effects accepted inputs) permutation order history member kind

end Airbender.UnifiedReduced.Caller
