import Human.Helpers.Memory.ROM
import Slop.Trace.InitialImage

namespace Airbender.Trace.ROM.Proofs
open Arithmetic

/-- A readable aligned public word is the exact subword-table input. -/
theorem words_at_address {before : Reference.RiscV.Sail.State} {address : BitVec 32}
    {value : BitVec 32} (aligned : address.toNat % 4 = 0)
    (read : (Cell.ram address).read before = .ok value before) :
    words before (address.toNat / 4) = value := by
  have index : 4 * (address.toNat / 4) = address.toNat := by omega
  unfold words
  rw [index]
  change (match (Cell.ram address).read before with
    | .ok value _ => value
    | .error _ _ => 0) = value
  rw [read]

private theorem zip_source {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens)
    {cell : Cell} {token : MemoryToken p} (member : (cell, token) ∈ cells.zip tokens) :
    ∃ bits, cell.read before = .ok bits before ∧ token = cell.initialToken bits := by
  have sources := Trace.Proofs.image_reads image
  clear image
  induction sources with
  | nil => simp at member
  | @cons first value cells tokens head tail ih =>
    simp only [List.zip_cons_cons, List.mem_cons] at member
    rcases member with equal | member
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact head
    · exact ih member

theorem member {p : Nat} [Fact p.Prime] {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImage before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (table cells tokens).Contains #[] query) :
    query = Vector.replicate 9 0 ∨ ∃ address bits, Cell.ram address ∈ cells ∧ address.toNat < limit ∧
      (Cell.ram address).read before = .ok bits before ∧ query = row address (Word.ofBitVec bits) := by
  obtain ⟨i, equal⟩ := contains
  have present : query ∈ rows cells tokens := equal ▸ List.get_mem _ i
  simp only [rows, List.mem_cons, List.mem_filterMap] at present
  rcases present with zero | ⟨⟨cell, token⟩, zipped, mapped⟩
  · exact Or.inl zero
  · obtain ⟨bits, read, source⟩ := zip_source image zipped
    cases cell with
    | register index => simp at mapped
    | ram address =>
      by_cases low : address.toNat < limit
      · simp only [low, ite_true, Option.some.injEq] at mapped
        right
        refine ⟨address, bits, ?_, low, read, ?_⟩
        · exact (List.of_mem_zip zipped).1
        · rw [← mapped, source, Trace.Proofs.initial_token_word]
      · simp [low] at mapped

theorem bounds {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImage before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (table cells tokens).Contains #[] query) :
    query[1].val < limbBase ∧ query[2].val < limbBase := by
  rcases member image contains with rfl | ⟨address, bits, _, _, _, rfl⟩
  · simp [limbBase]
  · have bound := Word.ofBitVec_bound bits
    change ((Word.ofBitVec bits).lo : ZMod p).val < limbBase ∧
      ((Word.ofBitVec bits).hi : ZMod p).val < limbBase
    rw [ZMod.val_natCast_of_lt (lt_trans bound.1 hp), ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]
    exact bound

theorem disabled {p : Nat} [Fact p.Prime] (hp : 34 < p)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImage before cells = some tokens) {query : Vector (ZMod p) 9}
    (contains : (table cells tokens).Contains #[] query) (inactive : query[8] = 0) :
    query[1] = 0 ∧ query[2] = 0 := by
  rcases member image contains with rfl | ⟨address, bits, _, _, _, same⟩
  · exact ⟨rfl, rfl⟩
  · rw [same] at inactive
    have tag : (34 : ZMod p) = 0 := inactive
    have value := congrArg ZMod.val tag
    have nonzero : ((34 : Nat) : ZMod p).val = 34 := ZMod.val_natCast_of_lt hp
    norm_num only [Nat.cast_ofNat] at nonzero
    rw [nonzero, ZMod.val_zero] at value
    contradiction

theorem value_boundary {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (setup : trace.rom = table cells trace.initialMemory) : ValueBoundary trace := by
  constructor
  · exact Trace.Proofs.image_bounds image
  · intro query contains inactive
    rw [setup] at contains
    exact disabled (by dsimp [limbBase] at hp; omega) image contains inactive
  · intro query contains
    rw [setup] at contains
    exact bounds hp image contains

/-- A ROM query reads the bytes of its public Sail cell, rather than a separately
    supplied expected value. Canonical addresses exclude field-wrap aliases. -/
theorem read_source {p : Nat} [Fact p.Prime] (hp : limit < p)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImage before cells = some tokens) (address : Word) (lo hi : ZMod p)
    (bounded : address.Bounded) (low : address.hi < 64)
    (contains : (table cells tokens).Contains #[]
      #v[(address.lo : ZMod p) + 65536 * address.hi, lo, hi, 0, 0, 0, 0, 0, 34]) :
    Cell.ram address.toBitVec ∈ cells ∧
      (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 address.toBitVec.toNat).run before =
        .ok (Word.mk lo.val hi.val).toBitVec before := by
  have small : address.value < limit := by
    dsimp [Word.value, Word.Bounded, limbBase, limit] at *
    omega
  have modulus : limbBase < p := by dsimp [limbBase, limit] at *; omega
  rcases member image contains with zero | ⟨source, bits, sourceMember, sourceLow, bytes, equal⟩
  · have tag := congrArg (fun query : Vector (ZMod p) 9 => query[8]) zero
    change (34 : ZMod p) = 0 at tag
    have values := congrArg ZMod.val tag
    have cast : ((34 : Nat) : ZMod p).val = 34 :=
      ZMod.val_natCast_of_lt (by dsimp [limit] at hp; omega)
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
      rw [Nat.mod_eq_of_lt (by dsimp [limit] at small; omega)]
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
    exact ⟨sourceMember, bytes⟩

theorem read {p : Nat} [Fact p.Prime] (hp : limit < p)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImage before cells = some tokens) (address : Word) (lo hi : ZMod p)
    (bounded : address.Bounded) (low : address.hi < 64)
    (contains : (table cells tokens).Contains #[]
      #v[(address.lo : ZMod p) + 65536 * address.hi, lo, hi, 0, 0, 0, 0, 0, 34]) :
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 address.toBitVec.toNat).run before =
      .ok (Word.mk lo.val hi.val).toBitVec before :=
  (read_source hp image address lo hi bounded low contains).2

end Airbender.Trace.ROM.Proofs
