import Airbender.Review.Helpers.UnifiedReduced.NativeMemory
import Airbender.Proofs.UnifiedReduced.PathCallABI
import Airbender.Proofs.Blake2G.NativeValidity
import Airbender.Proofs.Blake2Round.NativeValidity
import Airbender.Proofs.Keccak.NativeValidity

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false

/-- Round-mask validity is now a native consequence, before shared-history
construction; it is absent from the public boundary of the new entrypoint. -/
theorem native_round_masks {data : RequestTrace babyBearModulus}
    {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputs data program initial ca oa cells) :
    ∀ row ∈ data.workers.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  intro row member family
  obtain ⟨family', w⟩ := row
  change family' = .blakeRound at family
  subst family'
  have core := accepted.workerConstraints ⟨.blakeRound, w⟩ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Blake2Round.clockConstraints data.workers.setup.blakeRound) at core
  rw [inputs.tables] at core
  have core := Verification.holds_of_sublist core
    (List.sublist_append_left (Blake2Round.importedConstraints Blake2Round.setupTable)
      Blake2Round.importedConstraintsTimestampLookups)
  exact Blake2Round.Proofs.successful_mask core (accepted.workerActive _ member)

theorem native_memory_inputs {data : RequestTrace babyBearModulus}
    {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputs data program initial ca oa cells) :
    MixedMemoryInputs data program initial ca oa cells :=
  ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables, native_round_masks accepted inputs⟩

/-- Native constraints derive every local successful hash controller and G
base separation. There is no occurrence plan or controller-preparation premise.
The existing separate bigint command contract remains explicit. -/
theorem native_worker_call
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} {worker : Delegation.Row babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    (commands : BigintCommands data) (member : worker ∈ data.workers.rows)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before) :
    FullCall worker.family before after := by
  have effects := mixed_memory_effects accepted inputs
  have core := accepted.workerConstraints worker member
  have active := accepted.workerActive worker member
  cases worker with
  | mk family w =>
    cases family with
    | bigint =>
      exact path_worker_call accepted inputs ram commands .bigint member rfl trivial
        history permutation observed
    | blakeG =>
      change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
        (Blake2G.clockConstraints data.workers.setup.blakeG) at core
      rw [inputs.tables] at core
      have core := Verification.holds_of_sublist core (List.sublist_append_left
        (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows))
        Blake2G.importedConstraintsTimestampLookups)
      have bounds (i : Fin 9) := (effects.words _
        (mixed_worker_member member (Array.getElem_mem i.isLt))).1
      have controlBound : (w 3).val < 65536 := by
        have bounded := bounds 8
        simpa [Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts,
          Trace.Proofs.read_word, WordColumns.evaluate, limbBase] using bounded.1
      obtain ⟨reduced, index, control⟩ := Blake2G.Proofs.successful_position core active controlBound
      have pointers : PathGPointerBinding ⟨.blakeG, w⟩ :=
        Blake2G.Proofs.successful_bases core active ⟨bounds 0, bounds 5⟩
      exact path_worker_call accepted inputs ram commands (.hash ⟨.blakeG reduced, index⟩)
        member ⟨rfl, control⟩ pointers history permutation observed
    | blakeRound =>
      change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
        (Blake2Round.clockConstraints data.workers.setup.blakeRound) at core
      rw [inputs.tables] at core
      have core := Verification.holds_of_sublist core (List.sublist_append_left
        (Blake2Round.importedConstraints Blake2Round.setupTable)
        Blake2Round.importedConstraintsTimestampLookups)
      obtain ⟨flags, index, control⟩ := Blake2Round.Proofs.successful_position core active
      exact path_worker_call accepted inputs ram commands (.hash ⟨.blakeRound flags, index⟩)
        member ⟨rfl, control⟩ trivial history permutation observed
    | keccak =>
      change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
        (Keccak.clockConstraints data.workers.setup.keccak) at core
      rw [inputs.tables] at core
      have core := Verification.holds_of_sublist core (List.sublist_append_left
        (Keccak.importedConstraints (Keccak.setupTable Keccak.Controller.rows))
        Keccak.importedConstraintsTimestampLookups)
      obtain ⟨index, control⟩ := Keccak.Proofs.successful_position core active
      exact path_worker_call accepted inputs ram commands (.hash ⟨.keccak, index⟩)
        member ⟨rfl, control⟩ trivial history permutation observed

end Airbender.UnifiedReduced.Caller.Proofs
