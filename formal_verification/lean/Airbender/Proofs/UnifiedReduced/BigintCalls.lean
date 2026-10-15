import Airbender.Review.Trace.UnifiedReduced.BigintCycles
import Airbender.Proofs.Bigint.NativeCall
import Airbender.Proofs.UnifiedReduced.WorkerABI
import Airbender.Proofs.UnifiedReduced.MixedCycleComposition

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

theorem bigint_of_csr {family : Delegation.Family}
    (same : Delegation.Requests.csr family = Delegation.Requests.csr .bigint) : family = .bigint := by
  cases family <;> simp_all [Delegation.Requests.csr]

theorem bigint_call_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells) (commands : BigintCommands data)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.callers)
    (kind : (request row.assignment).csr = Delegation.Requests.csr .bigint) :
    BigintCallCycle data initial finalState cells events row := by
  obtain ⟨before, after, past, current, future,
    ⟨entry, present, query, pc, source, worker, included, matched, family, _, observed⟩, retired⟩ :=
      native_caller_cycles_at accepted inputs code effects permutation order history row member
  have workerKind : worker.family = .bigint := by
    have csr := congrArg Delegation.Requests.Request.csr matched
    change Delegation.Requests.csr worker.family = (request row.assignment).csr at csr
    rw [kind] at csr
    exact bigint_of_csr csr
  have nativeMember := List.mem_of_mem_filter member
  have positive := machine_native_clock_positive (by decide) (by decide) accepted
    inputs.publicProgram inputs.initialization nativeMember
  have positive : 0 < Delegation.Caller.startClock row := by omega
  have cycle := cycle_window_permutation (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
    effects.requests permutation nativeMember positive
  obtain ⟨actual, actualMember, actualMatch, grouped, localHistory⟩ :=
    caller_cycle_worker_history effects.requests member cycle current
  obtain ⟨_, _, unique⟩ := Delegation.Requests.Proofs.unique_fulfillment
    effects.requests.fulfilled effects.requests.invocations.1 (List.mem_map.mpr ⟨row, member, rfl⟩)
  have same : actual = worker := (unique actual ⟨actualMember, actualMatch⟩).trans
    (unique worker ⟨included, matched⟩).symm
  subst actual
  have abi := bigint_pointer_abi accepted inputs code.ram worker included workerKind
  obtain ⟨command, binding⟩ := commands worker included workerKind
  have core := accepted.workerConstraints worker included
  rcases worker with ⟨workerFamily, w⟩
  change workerFamily = .bigint at workerKind
  subst workerFamily
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Bigint.clockConstraints data.workers.setup.bigint) at core
  rw [inputs.tables] at core
  have core := Verification.holds_of_sublist core
    (List.sublist_append_left (Bigint.importedConstraints Bigint.setupTable) Bigint.importedConstraintsTimestampLookups)
  have execution := Bigint.Call.Proofs.executes (w := w) (command := command) core abi binding
    (retired_state_history localHistory row.start.word.toBitVec) grouped (fun port portMember => by
      obtain ⟨cell, _, address, read, _⟩ := observed port (by
        change port ∈ Bigint.importedConstraintsMemoryPorts
        exact portMember)
      exact ⟨cell, address, read⟩)
  exact ⟨before, after, past, current, future,
    ⟨entry, present, family.symm.trans rfl, query, pc, source⟩, _, execution, retired⟩

end Airbender.UnifiedReduced.Caller.Proofs
