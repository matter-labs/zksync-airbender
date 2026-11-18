module
public import Human.Helpers.Delegation.RVMemory
public import Proven.Delegation.SeedMemory
public import Proven.Trace.RVTransfer

@[expose] public section

/-! The RV public inputs of a delegation pool at the proof level: the state-free seed facts (`SeedProofs.SeedInputs`)
    plus each seed token's read from the starting `RV.State`, built from the human `RVMemoryInputs`. -/

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true

/-- RV sibling of `BoundaryInputs`: the state-free seed facts and each seed token's RV read. A RAM cell is RAM at
    any address, the shadow RAM below `ROM_END` included. -/
structure RVBoundaryInputs (data : MemoryData p) (before : RV.State) (cells : List Cell) : Prop
    extends toSeed : SeedProofs.SeedInputs data cells where
  reads : ∀ token ∈ data.initial, ∃ cell ∈ cells, cell.addressCode = token.address ∧
    cell.readRV before = some (memoryWord token.value)

theorem RVBoundaryInputs.transfer {data : MemoryData p} {before : RV.State} {cells : List Cell}
    (inputs : RVBoundaryInputs data before cells) :
    Transfer.RVBoundaryInputs (transferData data) before cells :=
  ⟨inputs.toSeed.toSeedInputs, inputs.reads⟩

/-- Each RV seed token is a public cell's `initialToken` of its starting RV read (`RVZero.rv_image_token_sources`,
    restated here to keep this module off the RV program table). -/
private theorem rv_image_sources {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens) :
    ∀ token ∈ tokens, ∃ cell ∈ cells, ∃ value,
      cell.readRV before = some value ∧ token = cell.initialToken value := by
  have reads := rvImage_reads cells tokens image
  clear image
  induction reads with
  | nil => simp
  | @cons cell token cells tokens head tail ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨value, read, same⟩ := head
      exact ⟨cell, List.mem_cons_self, value, read, same⟩
    · obtain ⟨source, sourceMember, value, read, same⟩ := ih actual member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, value, read, same⟩

end Airbender.Delegation.Proofs

namespace Airbender.Delegation
open Trace Trace.Proofs Arithmetic

theorem RVMemoryInputs.toRVBoundaryInputs {data : MemoryData p} {before : RV.State} {cells : List Cell}
    (inputs : RVMemoryInputs data before cells) : Proofs.RVBoundaryInputs data before cells := by
  have sources := Proofs.rv_image_sources inputs.initialization
  refine ⟨⟨⟨?_, inputs.distinct⟩, ?_, ?_, inputs.clockRoom, inputs.invocationHigh⟩, ?_⟩
  · change (data.initial.map MemoryToken.address).Perm (cells.map Cell.addressCode)
    rw [rvImage_addresses inputs.initialization]
  · intro token member
    obtain ⟨cell, _, value, _, rfl⟩ := sources token member
    rw [initial_token_word]
    exact Word.ofBitVec_bound value
  · intro token member
    obtain ⟨cell, _, value, _, rfl⟩ := sources token member
    simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]
  · intro token member
    obtain ⟨cell, present, value, read, rfl⟩ := sources token member
    refine ⟨cell, present, rfl, ?_⟩
    simp only [Cell.initialToken, memoryWord, Nat.unpair_pair]
    rw [Word.ofBitVec_roundtrip]
    exact read

end Airbender.Delegation
