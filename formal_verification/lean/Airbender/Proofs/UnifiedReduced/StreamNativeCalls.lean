import Airbender.Proofs.UnifiedReduced.StreamPathCallABI
import Airbender.Proofs.UnifiedReduced.NativeCalls

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
open Caller.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Native packing derives the round mask from the explicit controller contract. -/
theorem native_round_masks {data : RequestTrace babyBearModulus}
    {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
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

/-- Native worker controllers supply the shared stream-registry memory effects. -/
theorem native_memory_effects {data : RequestTrace babyBearModulus}
    {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (hashes : HashCommands data) : MixedMemoryEffects data initial cells :=
  memory_effects accepted inputs (native_round_masks accepted inputs hashes)

/-- Actual native worker calls use explicit bigint and hash input contracts. -/
theorem native_worker_call
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} {worker : Delegation.Row babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
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
      exact path_worker_call accepted inputs effects ram commands .bigint member rfl trivial
        history permutation observed
    | blakeG =>
      obtain ⟨reduced, index, control⟩ := hashes.gControl w member
      have pointers : PathGPointerBinding ⟨.blakeG, w⟩ :=
        hashes.gBases w member
      exact path_worker_call accepted inputs effects ram commands (.hash ⟨.blakeG reduced, index⟩)
        member ⟨rfl, control⟩ pointers history permutation observed
    | blakeRound =>
      obtain ⟨flags, index, bound, control⟩ := hashes.roundControl w member
      exact path_worker_call accepted inputs effects ram commands (.hash ⟨.blakeRound flags, ⟨index.val, bound⟩⟩)
        member ⟨rfl, control⟩ trivial history permutation observed
    | keccak =>
      obtain ⟨index, control⟩ := hashes.keccakControl w member
      exact path_worker_call accepted inputs effects ram commands (.hash ⟨.keccak, index⟩)
        member ⟨rfl, control⟩ trivial history permutation observed

end Airbender.UnifiedReduced.Caller.Stream.Proofs
