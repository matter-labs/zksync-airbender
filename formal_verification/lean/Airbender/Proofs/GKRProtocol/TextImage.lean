import Airbender.Review.Helpers.Memory.TextImage
import Airbender.Proofs.Trace.InitialImage

namespace Airbender.Trace.ROM.Proofs

private theorem image_zip_member {p : Nat}
    {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken p)}
    (physical : Trace.initialImage before cells = some tokens)
    {cell : Trace.Cell} (member : cell ∈ cells) {bits : BitVec 32}
    (read : cell.read before = .ok bits before) :
    (cell, cell.initialToken bits) ∈ cells.zip tokens := by
  have reads := Trace.Proofs.image_reads physical
  clear physical
  induction reads with
  | nil => cases member
  | @cons head token cells tokens headEvidence tail ih =>
    rcases List.mem_cons.mp member with same | included
    · subst cell
      obtain ⟨value, found, rfl⟩ := headEvidence
      have equal : value = bits := (EStateM.Result.ok.inj (found.symm.trans read)).1
      subst value
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih included)

theorem words_of_text_image (before : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (image : TextImage before text)
    (index : Fin text.length) : words before index.val = text[index.val] := by
  simp [words, image index]

theorem bytes_of_text_image (before : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (image : TextImage before text)
    (fits : text.length ≤ limit / 4) (index : Fin text.length) :
    (Trace.Cell.ram (BitVec.ofNat 32 (4 * index.val))).read before =
      .ok text[index.val] before := by
  have bound : 4 * index.val < 2 ^ 32 := by
    have h := Nat.lt_of_lt_of_le index.isLt fits
    unfold limit at h
    omega
  change (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4
    (BitVec.ofNat 32 (4 * index.val)).toNat).run before = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  exact image index

/-- A public text word that is present in the initial cell image has the
corresponding row in the modeled word ROM. This holds for arbitrary text and
does not consult the retained native ROM capture. -/
theorem text_row_member {p : Nat} [Fact p.Prime]
    (before : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (image : TextImage before text) (fits : text.length ≤ limit / 4)
    (cells : List Trace.Cell) (tokens : List (Trace.MemoryToken p))
    (physical : Trace.initialImage before cells = some tokens)
    (index : Fin text.length)
    (domain : Trace.Cell.ram (BitVec.ofNat 32 (4 * index.val)) ∈ cells) :
    (table cells tokens).Contains #[]
      (row (BitVec.ofNat 32 (4 * index.val))
        (Arithmetic.Word.ofBitVec text[index.val])) := by
  let address := BitVec.ofNat 32 (4 * index.val)
  have bound : 4 * index.val < 2 ^ 32 := by
    have h := Nat.lt_of_lt_of_le index.isLt fits
    unfold limit at h
    omega
  have low : address.toNat < limit := by
    have h := Nat.lt_of_lt_of_le index.isLt fits
    simp only [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega
  have read : (Trace.Cell.ram address).read before = .ok text[index.val] before :=
    bytes_of_text_image before text image fits index
  have zipped := image_zip_member physical domain read
  have present : row address (Arithmetic.Word.ofBitVec text[index.val]) ∈
      rows cells tokens := by
    apply List.mem_cons_of_mem
    apply List.mem_filterMap.mpr
    refine ⟨(Trace.Cell.ram address,
      (Trace.Cell.ram address).initialToken text[index.val]), zipped, ?_⟩
    simp only [low, if_true, Trace.Proofs.initial_token_word]
  exact (table cells tokens).implied_by_completeness #[] _ present

end Airbender.Trace.ROM.Proofs
