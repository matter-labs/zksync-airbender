import Slop.Trace.RVValues

/-! RV twin of `ROM.Proofs.read_source`: an active word-ROM query reads the public RV starting bytes of its address
    (`RV.read initial.mem`), not a separately supplied value. `rv_rom_member` (RVValues.lean) forgets the read; this
    keeps it. -/

namespace Airbender.Trace.RVValues
open Arithmetic Trace.Proofs

private theorem rv_zip_read {p : Nat} {before : RV.State} {cells : List Cell}
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

/-- `rv_rom_member` keeping the read: a word-ROM row is the padding row or the starting word of a public RAM cell
    below `ROM.limit`. -/
theorem rv_rom_member_read {p : Nat} [Fact p.Prime] {before : RV.State}
    {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (ROM.table cells tokens).Contains #[] query) :
    query = Vector.replicate 9 0 ∨ ∃ address bits, Cell.ram address ∈ cells ∧ address.toNat < ROM.limit ∧
      (Cell.ram address).readRV before = some bits ∧ query = ROM.row address (Word.ofBitVec bits) := by
  obtain ⟨i, equal⟩ := contains
  have present : query ∈ ROM.rows cells tokens := equal ▸ List.get_mem _ i
  simp only [ROM.rows, List.mem_cons, List.mem_filterMap] at present
  rcases present with zero | ⟨⟨cell, token⟩, zipped, mapped⟩
  · exact Or.inl zero
  · obtain ⟨bits, read, source⟩ := rv_zip_read image zipped
    cases cell with
    | register index => simp at mapped
    | ram address =>
      by_cases low : address.toNat < ROM.limit
      · simp only [low, ite_true, Option.some.injEq] at mapped
        right
        refine ⟨address, bits, ?_, low, read, ?_⟩
        · exact (List.of_mem_zip zipped).1
        · rw [← mapped, source, initial_token_word]
      · simp [low] at mapped

/-- An active ROM query at a canonical address below `ROM.limit` reads the public cell's starting bytes. -/
theorem rv_rom_read {p : Nat} [Fact p.Prime] (hp : ROM.limit < p)
    {before : RV.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImageRV before cells = some tokens) (address : Word) (lo hi : ZMod p)
    (bounded : address.Bounded) (low : address.hi < 64)
    (contains : (ROM.table cells tokens).Contains #[]
      #v[(address.lo : ZMod p) + 65536 * address.hi, lo, hi, 0, 0, 0, 0, 0, 34]) :
    Cell.ram address.toBitVec ∈ cells ∧
      RV.read before.mem address.toBitVec 4 = (Word.mk lo.val hi.val).toBitVec := by
  have small : address.value < ROM.limit := by
    dsimp [Word.value, Word.Bounded, limbBase, ROM.limit] at *
    omega
  have modulus : limbBase < p := by dsimp [limbBase, ROM.limit] at *; omega
  rcases rv_rom_member_read image contains with zero | ⟨source, bits, sourceMember, sourceLow, read, equal⟩
  · have tag := congrArg (fun query : Vector (ZMod p) 9 => query[8]) zero
    change (34 : ZMod p) = 0 at tag
    have values := congrArg ZMod.val tag
    have cast : ((34 : Nat) : ZMod p).val = 34 :=
      ZMod.val_natCast_of_lt (by dsimp [ROM.limit] at hp; omega)
    norm_num only [Nat.cast_ofNat] at cast
    rw [cast, ZMod.val_zero] at values
    contradiction
  · have encoded := congrArg (fun query : Vector (ZMod p) 9 => query[0]) equal
    change (address.lo : ZMod p) + 65536 * address.hi = (source.toNat : ZMod p) at encoded
    have castAddress : (address.lo : ZMod p) + 65536 * address.hi = (address.value : ZMod p) := by
      simp [Word.value, limbBase]
    rw [castAddress] at encoded
    have natural := congrArg ZMod.val encoded
    rw [ZMod.val_natCast_of_lt (lt_trans small hp),
      ZMod.val_natCast_of_lt (lt_trans sourceLow hp)] at natural
    have sameAddress : address.toBitVec = source := by
      apply BitVec.eq_of_toNat_eq
      change address.value % 2 ^ 32 = source.toNat
      rw [Nat.mod_eq_of_lt (by dsimp [ROM.limit] at small; omega)]
      exact natural
    have lowWord := congrArg (fun query : Vector (ZMod p) 9 => query[1]) equal
    have highWord := congrArg (fun query : Vector (ZMod p) 9 => query[2]) equal
    change lo = ((Word.ofBitVec bits).lo : ZMod p) at lowWord
    change hi = ((Word.ofBitVec bits).hi : ZMod p) at highWord
    have bound := Word.ofBitVec_bound bits
    have word : Word.mk lo.val hi.val = Word.ofBitVec bits := by
      rw [lowWord, highWord, ZMod.val_natCast_of_lt (lt_trans bound.1 modulus),
        ZMod.val_natCast_of_lt (lt_trans bound.2 modulus)]
    rw [word, Word.ofBitVec_roundtrip, sameAddress]
    have readable := readable_of_readRV read
    rw [readRV_ram _ readable] at read
    exact ⟨sourceMember, Option.some.inj read⟩

end Airbender.Trace.RVValues
