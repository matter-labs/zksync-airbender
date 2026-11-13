module
public import Proven.Trace.RVTransfer
public import Proven.Trace.RVZero

@[expose] public section

/-! RV public-image facts used by the shared caller/worker pools (twins of `image_clocks`, `image_restriction`,
    `initial_zero` and `Transfer.Inputs`): the seed image is `initialImageRV` of an `RV.State`. -/

namespace Airbender.Trace.Proofs.Transfer
open Arithmetic
set_option warningAsError true

theorem rv_image_clocks {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens) :
    ∀ token ∈ tokens, (timeOfPair token.time).Bounded := by
  intro token member
  obtain ⟨cell, _, value, _, rfl⟩ := RVZero.rv_image_token_sources image token member
  simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]

/-- An x0 seed token of an RV image holds zero (`getReg 0 = 0`). -/
theorem rv_initial_zero {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens) :
    ∀ token ∈ tokens, token.address = (Cell.register 0).addressCode → token.value = 0 := by
  intro token present same
  obtain ⟨cell, _, value, read, rfl⟩ := RVZero.rv_image_token_sources image token present
  have code : cell.addressCode = (Cell.register 0).addressCode := same
  have equal := cell_address_injective code
  subst cell
  have actual : value = 0 := by
    change some (0 : BitVec 32) = some value at read
    exact (Option.some.inj read).symm
  subst value
  rfl

theorem rv_image_restriction {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens)
    (keep : Nat → Bool) :
    initialImageRV before (cells.filter fun cell => keep cell.addressCode) =
      some (tokens.filter fun token => keep token.address) := by
  have reads := rvImage_reads cells tokens image
  clear image
  induction reads with
  | nil => rfl
  | @cons cell token cells tokens head tail ih =>
    obtain ⟨value, read, rfl⟩ := head
    simp only [initialImageRV, Cell.initialToken] at ih
    cases selected : keep cell.addressCode <;>
      simp [Cell.initialToken, selected, initialImageRV, List.mapM_cons, read, ih]

/-- RV sibling of `Transfer.Inputs.toBoundaryInputs`: a public RV image with a distinct cell domain. -/
theorem rv_boundary_inputs {data : Data p} {before : RV.State} {cells : List Cell}
    (image : initialImageRV before cells = some data.initial)
    (distinct : (cells.map Cell.addressCode).Nodup) : RVBoundaryInputs data before cells := by
  refine ⟨⟨?_, distinct⟩, ?_⟩
  · rw [rvImage_addresses image]
  · intro token member
    obtain ⟨cell, present, value, read, rfl⟩ := RVZero.rv_image_token_sources image token member
    refine ⟨cell, present, rfl, ?_⟩
    simp only [Cell.initialToken, memoryWord, Nat.unpair_pair]
    rw [Word.ofBitVec_roundtrip]
    exact read

end Airbender.Trace.Proofs.Transfer
