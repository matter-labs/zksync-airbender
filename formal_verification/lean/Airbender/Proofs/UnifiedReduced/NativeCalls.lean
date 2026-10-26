import Airbender.Review.Helpers.UnifiedReduced.NativeMemory
import Airbender.Proofs.UnifiedReduced.PathCallABI
import Airbender.Proofs.Blake2Round.ExclusiveMask

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false

/-- Derive the bit-level mask from the explicit controller contract and the
restored native packing equations. The controller contract is not inferred. -/
theorem native_round_masks {data : RequestTrace babyBearModulus}
    {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputs data program initial ca oa cells)
    (hashes : HashCommands data) :
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
  obtain ⟨flags, round, _, control⟩ := hashes.roundControl w member
  have powerBound : 2 ^ round.val < 1024 := by fin_cases round <;> decide
  have packed : (w 136).val = flags.val + 8 * 2 ^ round.val := by
    have high := congrArg Word.hi control
    simpa [Trace.Proofs.read_word, Blake2Round.importedConstraintsMemoryPorts,
      WordColumns.evaluate, Blake2Round.controlAt, Nat.mod_eq_of_lt powerBound] using high
  exact ⟨round, (Blake2Round.Proofs.exclusive_mask_iff (by decide) core round).mpr ⟨flags, packed⟩⟩

theorem native_memory_inputs {data : RequestTrace babyBearModulus}
    {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputs data program initial ca oa cells)
    (hashes : HashCommands data) :
    MixedMemoryInputs data program initial ca oa cells :=
  ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables, native_round_masks accepted inputs hashes⟩

/-- Execute each worker under the explicit hash input contracts and the existing
bigint command contract. Native constraints and shared history derive effects;
controller membership and G base separation are assumptions. -/
theorem native_worker_call
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} {worker : Delegation.Row babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    (commands : BigintCommands data) (hashes : HashCommands data)
    (member : worker ∈ data.workers.rows)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before) :
    FullCall worker.family before after := by
  cases worker with
  | mk family w =>
    cases family with
    | bigint =>
      exact path_worker_call accepted inputs ram commands .bigint member rfl trivial
        history permutation observed
    | blakeG =>
      obtain ⟨reduced, index, control⟩ := hashes.gControl w member
      have pointers : PathGPointerBinding ⟨.blakeG, w⟩ :=
        hashes.gBases w member
      exact path_worker_call accepted inputs ram commands (.hash ⟨.blakeG reduced, index⟩)
        member ⟨rfl, control⟩ pointers history permutation observed
    | blakeRound =>
      obtain ⟨flags, index, bound, control⟩ := hashes.roundControl w member
      exact path_worker_call accepted inputs ram commands (.hash ⟨.blakeRound flags, ⟨index.val, bound⟩⟩)
        member ⟨rfl, control⟩ trivial history permutation observed
    | keccak =>
      obtain ⟨index, control⟩ := hashes.keccakControl w member
      exact path_worker_call accepted inputs ram commands (.hash ⟨.keccak, index⟩)
        member ⟨rfl, control⟩ trivial history permutation observed

end Airbender.UnifiedReduced.Caller.Proofs
