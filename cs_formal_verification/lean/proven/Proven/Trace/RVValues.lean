module
public import Proven.Trace.RVZero

@[expose] public section

/-! RV-route twin of `pooled_value_bounds` (`PooledValues.lean`): every native read, write and terminal word of an
    accepted pooled trace is bounded, from the RV public initialization (`initialImageRV`) and the RV program table
    (`rvProgramImageWith rvPooledDecoderFields`). No Sail state, `Configured` or interpreter fact.

    Changes from the Sail proof: the seed facts read `initialImageRV` (`rvImage_reads`), the ROM-table facts the ROM
    image (`romImageRV`); the two family
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

/-- A pair of the ROM image's zip with the public cells: the cell is public and the token is its ROM-image word. -/
private theorem rv_rom_zip {p : Nat} {before : RV.State} {cells : List Cell} {cell : Cell}
    {token : MemoryToken p} (member : (cell, token) ∈ cells.zip (romImageRV before cells)) :
    cell ∈ cells ∧ ∀ address, cell = .ram address →
      token = cell.initialToken (RV.read before.rom address 4) := by
  unfold romImageRV at member
  induction cells with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at member
    rcases member with equal | member
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact ⟨List.mem_cons_self, fun address same => by subst same; rfl⟩
    · obtain ⟨present, word⟩ := ih member
      exact ⟨List.mem_cons_of_mem _ present, word⟩

/-- RV twin of `ROM.Proofs.member`: a word-ROM row is the padding row or the ROM image's word at a public RAM cell
    below `RV.ROM_END`. -/
theorem rv_rom_member {p : Nat} [Fact p.Prime] {before : RV.State} {cells : List Cell}
    {query : Vector (ZMod p) 9} (contains : (ROM.table cells (romImageRV before cells)).Contains #[] query) :
    query = Vector.replicate 9 0 ∨ ∃ address, Cell.ram address ∈ cells ∧ address.toNat < RV.ROM_END ∧
      query = ROM.row address (Word.ofBitVec (RV.read before.rom address 4)) := by
  obtain ⟨i, equal⟩ := contains
  have present : query ∈ ROM.rows cells (romImageRV before cells) := equal ▸ List.get_mem _ i
  simp only [ROM.rows, List.mem_cons, List.mem_filterMap] at present
  rcases present with zero | ⟨⟨cell, token⟩, zipped, mapped⟩
  · exact Or.inl zero
  · obtain ⟨member, source⟩ := rv_rom_zip zipped
    cases cell with
    | register index => simp at mapped
    | ram address =>
      by_cases low : address.toNat < RV.ROM_END
      · simp only [low, ite_true, Option.some.injEq] at mapped
        right
        refine ⟨address, member, low, ?_⟩
        rw [← mapped, source address rfl, initial_token_word]
      · simp [low] at mapped

theorem rv_rom_bounds {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {before : RV.State} {cells : List Cell} {query : Vector (ZMod p) 9}
    (contains : (ROM.table cells (romImageRV before cells)).Contains #[] query) :
    query[1].val < limbBase ∧ query[2].val < limbBase := by
  rcases rv_rom_member contains with rfl | ⟨address, _, _, rfl⟩
  · simp [limbBase]
  · have bound := Word.ofBitVec_bound (RV.read before.rom address 4)
    change ((Word.ofBitVec (RV.read before.rom address 4)).lo : ZMod p).val < limbBase ∧
      ((Word.ofBitVec (RV.read before.rom address 4)).hi : ZMod p).val < limbBase
    rw [ZMod.val_natCast_of_lt (lt_trans bound.1 hp), ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]
    exact bound

theorem rv_rom_disabled {p : Nat} [Fact p.Prime] (hp : 34 < p)
    {before : RV.State} {cells : List Cell} {query : Vector (ZMod p) 9}
    (contains : (ROM.table cells (romImageRV before cells)).Contains #[] query) (inactive : query[8] = 0) :
    query[1] = 0 ∧ query[2] = 0 := by
  rcases rv_rom_member contains with rfl | ⟨address, _, _, same⟩
  · exact ⟨rfl, rfl⟩
  · rw [same] at inactive
    have tag : (34 : ZMod p) = 0 := inactive
    have value := congrArg ZMod.val tag
    have nonzero : ((34 : Nat) : ZMod p).val = 34 := ZMod.val_natCast_of_lt hp
    norm_num only [Nat.cast_ofNat] at nonzero
    rw [nonzero, ZMod.val_zero] at value
    exact absurd value (by decide)

end Airbender.Trace.RVValues
