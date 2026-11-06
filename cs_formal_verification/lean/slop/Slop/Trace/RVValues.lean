import Slop.Trace.Values
import Slop.Trace.RVZero

/-! RV-route twin of `pooled_value_bounds` (`PooledValues.lean`): every native read, write and terminal word of an
    accepted pooled trace is bounded, from the RV public initialization (`initialImageRV`) and the RV program table
    (`rvProgramImageWith rvPooledDecoderFields`). No Sail state, `Configured` or interpreter fact.

    Changes from the Sail proof: the seed and ROM-table facts read `initialImageRV` (`rvImage_reads`); the two family
    lemmas that took a Sail `Fetched` (jump/branch destination, shift/binop destination) take the RV projection
    equation `fields` (`rvDecoderFields i = some data`) instead, which is all their proofs read. The chronological induction (`read_bounds_of_rules`, ...) is
    state-free and reused. -/

namespace Airbender.Trace.RVValues
open Arithmetic Trace.Proofs

/-- Initial RV tokens carry canonical words. -/
theorem rv_image_bounds {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens) :
    ∀ token ∈ tokens, token.word.Bounded := by
  intro token member
  obtain ⟨cell, _, value, _, rfl⟩ := RVZero.rv_image_token_sources image token member
  rw [initial_token_word]
  exact Word.ofBitVec_bound value

private theorem rv_zip_source {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens)
    {cell : Cell} {token : MemoryToken p} (member : (cell, token) ∈ cells.zip tokens) :
    ∃ bits, cell.readRV before = some bits ∧ token = cell.initialToken bits := by
  have sources := rvImage_reads cells tokens image
  clear image
  induction sources with
  | nil => simp at member
  | @cons first value cells tokens head tail ih =>
    simp only [List.zip_cons_cons, List.mem_cons] at member
    rcases member with equal | member
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact head
    · exact ih member

/-- RV twin of `ROM.Proofs.member`: a word-ROM row is the padding row or a public RAM cell's initial word. -/
theorem rv_rom_member {p : Nat} [Fact p.Prime] {before : RV.State}
    {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (ROM.table cells tokens).Contains #[] query) :
    query = Vector.replicate 9 0 ∨ ∃ address bits, Cell.ram address ∈ cells ∧ address.toNat < ROM.limit ∧
      query = ROM.row address (Word.ofBitVec bits) := by
  obtain ⟨i, equal⟩ := contains
  have present : query ∈ ROM.rows cells tokens := equal ▸ List.get_mem _ i
  simp only [ROM.rows, List.mem_cons, List.mem_filterMap] at present
  rcases present with zero | ⟨⟨cell, token⟩, zipped, mapped⟩
  · exact Or.inl zero
  · obtain ⟨bits, _, source⟩ := rv_zip_source image zipped
    cases cell with
    | register index => simp at mapped
    | ram address =>
      by_cases low : address.toNat < ROM.limit
      · simp only [low, ite_true, Option.some.injEq] at mapped
        right
        refine ⟨address, bits, ?_, low, ?_⟩
        · exact (List.of_mem_zip zipped).1
        · rw [← mapped, source, initial_token_word]
      · simp [low] at mapped

theorem rv_rom_bounds {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {before : RV.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (ROM.table cells tokens).Contains #[] query) :
    query[1].val < limbBase ∧ query[2].val < limbBase := by
  rcases rv_rom_member image contains with rfl | ⟨address, bits, _, _, rfl⟩
  · simp [limbBase]
  · have bound := Word.ofBitVec_bound bits
    change ((Word.ofBitVec bits).lo : ZMod p).val < limbBase ∧
      ((Word.ofBitVec bits).hi : ZMod p).val < limbBase
    rw [ZMod.val_natCast_of_lt (lt_trans bound.1 hp), ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]
    exact bound

theorem rv_rom_disabled {p : Nat} [Fact p.Prime] (hp : 34 < p)
    {before : RV.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (ROM.table cells tokens).Contains #[] query) (inactive : query[8] = 0) :
    query[1] = 0 ∧ query[2] = 0 := by
  rcases rv_rom_member image contains with rfl | ⟨address, bits, _, _, same⟩
  · exact ⟨rfl, rfl⟩
  · rw [same] at inactive
    have tag : (34 : ZMod p) = 0 := inactive
    have value := congrArg ZMod.val tag
    have nonzero : ((34 : Nat) : ZMod p).val = 34 := ZMod.val_natCast_of_lt hp
    norm_num only [Nat.cast_ofNat] at nonzero
    rw [nonzero, ZMod.val_zero] at value
    exact absurd value (by decide)

end Airbender.Trace.RVValues
