import Airbender.Review.Helpers.Decoder.ProgramRows
import Airbender.Review.Helpers.Memory.TextImage
import Airbender.Proofs.GKRProtocol.PublicProgram

namespace Airbender.Trace.NativeDecoder.ProgramRows.Proofs
open Airbender.Trace.NativeDecoder.ProgramRows

/-- Every ordinary entry projected from admitted public text has its actual
bytes and pure Sail decoding in the supplied initial state. Requiring a pure
decoder result avoids silently dropping decoder state effects. -/
theorem program_sources (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    ∀ entry ∈ programOf config initial text,
      entry.SourceWith initial config.fields := by
  intro entry member
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  have found : text[index]? = some bits := List.mk_mem_zipIdx_iff_getElem?.mp inText
  have indexBound : index < text.length := by
    by_contra notBound
    have : text[index]? = none := by simp [Nat.le_of_not_gt notBound]
    rw [this] at found
    contradiction
  have wordBound : 4 * index < 2 ^ 32 := by
    have h := Nat.lt_of_lt_of_le indexBound size
    unfold ROM.limit at h
    omega
  have bytes : (Trace.Cell.ram (BitVec.ofNat 32 (4 * index))).read initial =
      .ok bits initial := by
    change (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4
      (BitVec.ofNat 32 (4 * index)).toNat).run initial = .ok bits initial
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound]
    have h := image ⟨index, indexBound⟩
    have value : text[index] = bits := by
      have : text[index]? = some text[index] := by simp [indexBound]
      rw [this] at found
      exact Option.some.inj found
    simpa [value] using h
  unfold wordEntry at selected
  cases decoded : SailRV32.Functions.encdec_backwards bits with
  | pure instruction =>
    cases fields : config.fields instruction with
    | none => simp [decoded, fields] at selected
    | some data =>
      simp only [decoded, fields, bind, Option.bind] at selected
      change (some ⟨BitVec.ofNat 32 (4 * index), bits, instruction, data⟩ :
        Option PooledProgramEntry) = some entry at selected
      cases selected
      exact ⟨bytes, by rw [decoded]; rfl, fields⟩
  | impure call continuation => simp [decoded] at selected

/-- The whole ordinary program image is reconstructed by stateful Sail reads
from public text. Unsupported words stay absent from the logical program. -/
theorem program_image (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    programImageRunWith config.fields initial
      ((programOf config initial text).map ProgramEntry.pc) =
        some (programOf config initial text) :=
  Airbender.Compiler.PublicProgram.image_run _
    (program_sources config initial text image size)

/-- Native preprocessing rejects a text longer than the ROM capacity. For an
admitted text, the modeled decoder has exactly one row per padded word. -/
theorem rows_length {p : Nat} (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity) (family : PooledFamily) :
    (rows (p := p) config initial text capacity fits family).length = capacity := by
  simp [rows]
  omega

theorem native_decoder_rows_length {p : Nat} (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity) (family : PooledFamily)
    (mask : Mask) :
    (nativeDecoderRows (p := p) config initial text capacity fits family mask).length =
      capacity := by
  simp [nativeDecoderRows, nativeRows]
  omega

/-- A non-sentinel row of the program-derived decoder model has an actual
Sail-decoded public entry of the selected native family. This is a logical
fact about the Lean model; the Rust differential binding remains open. -/
theorem active_member {p : Nat} (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity)
    (family : PooledFamily) (query : Vector (ZMod p) 9)
    (member : query ∈ rows config initial text capacity fits family)
    (active : query ≠ sentinel) :
    ∃ entry ∈ programOf config initial text,
      entry.data.family = family ∧ query = entry.query := by
  rcases List.mem_append.mp member with source | padding
  · rcases List.mem_map.mp source with ⟨pair, inText, rowEq⟩
    rcases pair with ⟨bits, index⟩
    cases entryEq : wordEntry config initial bits index with
    | none =>
        have hs : query = sentinel := by simpa [familyRow, entryEq] using rowEq.symm
        exact (active hs).elim
    | some entry =>
        by_cases selected : entry.data.family = family
        · have inProgram : entry ∈ programOf config initial text := by
            exact List.mem_filterMap.mpr ⟨(bits, index), inText, entryEq⟩
          have hq : query = entry.query := by
            simpa [familyRow, entryEq, selected] using rowEq.symm
          exact ⟨entry, inProgram, selected, hq⟩
        · have hs : query = sentinel := by
            simpa [familyRow, entryEq, selected] using rowEq.symm
          exact (active hs).elim
  · have hs : query = sentinel := (List.mem_replicate.mp padding).2
    exact (active hs).elim

/-- Native rows include public delegation calls, whose virtual CSR cannot be
represented by the ordinary five-bit rs2 metadata. -/
theorem native_active_member {p : Nat} (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity)
    (family : PooledFamily) (query : Vector (ZMod p) 9)
    (member : query ∈ nativeRows config initial text capacity fits family)
    (active : query ≠ sentinel) :
    ∃ entry ∈ nativeProgramOf config initial text,
      entry.family = family ∧ query = entry.query := by
  rcases List.mem_append.mp member with source | padding
  · rcases List.mem_map.mp source with ⟨pair, inText, rowEq⟩
    rcases pair with ⟨bits, index⟩
    cases entryEq : nativeEntry config initial bits index with
    | none =>
        have hs : query = sentinel := by simpa [nativeFamilyRow, entryEq] using rowEq.symm
        exact (active hs).elim
    | some entry =>
        by_cases selected : entry.family = family
        · have inProgram : entry ∈ nativeProgramOf config initial text := by
            exact List.mem_filterMap.mpr ⟨(bits, index), inText, entryEq⟩
          have hq : query = entry.query := by
            simpa [nativeFamilyRow, entryEq, selected] using rowEq.symm
          exact ⟨entry, inProgram, selected, hq⟩
        · have hs : query = sentinel := by
            simpa [nativeFamilyRow, entryEq, selected] using rowEq.symm
          exact (active hs).elim
  · have hs : query = sentinel := (List.mem_replicate.mp padding).2
    exact (active hs).elim

/-- A selected masked row comes from a Sail-decoded public entry whenever it
is not the masked unsupported sentinel. This is independent of the text and
mask values; equality to native setup columns remains a separate premise. -/
theorem active_masked_member {p : Nat} (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity)
    (family : PooledFamily) (mask : Mask) (query : List (ZMod p))
    (member : query ∈ nativeDecoderRows config initial text capacity fits family mask)
    (active : query ≠ maskRow mask sentinel) :
    ∃ entry ∈ nativeProgramOf config initial text,
      entry.family = family ∧ query = maskRow mask entry.query := by
  obtain ⟨row, rowMember, rowEq⟩ := List.mem_map.mp member
  have nonSentinel : row ≠ sentinel := by
    intro equal
    exact active (rowEq.symm.trans (congrArg (maskRow mask) equal))
  obtain ⟨entry, inProgram, selected, fullEq⟩ :=
    native_active_member config initial text capacity fits family row rowMember nonSentinel
  exact ⟨entry, inProgram, selected,
    rowEq.symm.trans (congrArg (maskRow mask) fullEq)⟩

/-- The generic row lemma gives the existing logical decoder-table membership.
It does not claim that a Rust setup column equals this modeled row list. -/
theorem active_decoded {p : Nat} [Fact p.Prime] (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity)
    (family : PooledFamily) (query : Vector (ZMod p) 9)
    (member : query ∈ rows config initial text capacity fits family)
    (active : query ≠ sentinel) :
    (decoderTable (programOf config initial text) family).Contains #[] query := by
  obtain ⟨entry, inProgram, selected, hq⟩ :=
    active_member config initial text capacity fits family query member active
  apply (decoderTable (programOf config initial text) family).implied_by_completeness #[] query
  change ∃ entry ∈ programOf config initial text,
    entry.data.family = family ∧ query = entry.query
  exact ⟨entry, inProgram, selected, hq⟩

/-- The complete native row model admits ordinary instructions and public
delegation callers. Equality to Rust setup columns remains a separate premise. -/
theorem native_active_decoded {p : Nat} [Fact p.Prime] (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity)
    (family : PooledFamily) (query : Vector (ZMod p) 9)
    (member : query ∈ nativeRows config initial text capacity fits family)
    (active : query ≠ sentinel) :
    (nativeDecoderTable (nativeProgramOf config initial text) family).Contains #[] query := by
  obtain ⟨entry, inProgram, selected, hq⟩ :=
    native_active_member config initial text capacity fits family query member active
  apply (nativeDecoderTable (nativeProgramOf config initial text) family).implied_by_completeness #[] query
  change ∃ entry ∈ nativeProgramOf config initial text,
    entry.family = family ∧ query = entry.query
  exact ⟨entry, inProgram, selected, hq⟩

/-- The native 16-bit PC-limb range excludes the unsupported minus-one row
in the BabyBear field. -/
theorem bounded_pc_not_sentinel (query : Vector (ZMod babyBearModulus) 9)
    (bounded : query[0].val < 65536) : query ≠ sentinel := by
  intro equal
  have first := congrArg (fun row : Vector (ZMod babyBearModulus) 9 => row[0].val) equal
  have low : query[0].val = (-1 : ZMod babyBearModulus).val := by
    simpa [sentinel] using first
  have minusOne : (-1 : ZMod babyBearModulus).val = 2013265920 := by
    change (-1 : ZMod 2013265921).val = 2013265920
    exact ZMod.val_neg_one 2013265920
  have high : query[0].val = 2013265920 := by
    exact low.trans minusOne
  omega

/-- The first selected native column is the low PC limb, so the same native
range check excludes the masked unsupported row. -/
theorem bounded_masked_pc_not_sentinel (mask : Mask)
    (query : List (ZMod babyBearModulus))
    (bounded : (query.head?.getD 0).val < 65536) :
    query ≠ maskRow mask sentinel := by
  intro equal
  have first := congrArg
    (fun row : List (ZMod babyBearModulus) => (row.head?.getD 0).val) equal
  have low : (query.head?.getD 0).val = (-1 : ZMod babyBearModulus).val := by
    simpa [maskRow, sentinel] using first
  have minusOne : (-1 : ZMod babyBearModulus).val = 2013265920 := by
    change (-1 : ZMod 2013265921).val = 2013265920
    exact ZMod.val_neg_one 2013265920
  omega

/-- One public-text membership result for a range-checked active query after
applying its captured family mask. The native setup equality is still required
at the caller before this result can interpret an imported lookup row. -/
theorem bounded_masked_pc_decoded (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity) (family : PooledFamily)
    (mask : Mask) (query : List (ZMod babyBearModulus))
    (member : query ∈ nativeDecoderRows config initial text capacity fits family mask)
    (bounded : (query.head?.getD 0).val < 65536) :
    ∃ entry ∈ nativeProgramOf config initial text,
      entry.family = family ∧ query = maskRow mask entry.query :=
  active_masked_member config initial text capacity fits family mask query member
    (bounded_masked_pc_not_sentinel mask query bounded)

/-- One program-independent membership result for every selected active
decoder row of the modeled full or reduced setup. -/
theorem bounded_pc_decoded [Fact babyBearModulus.Prime] (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity) (family : PooledFamily)
    (query : Vector (ZMod babyBearModulus) 9)
    (member : query ∈ rows config initial text capacity fits family)
    (bounded : query[0].val < 65536) :
    (decoderTable (programOf config initial text) family).Contains #[] query :=
  active_decoded config initial text capacity fits family query member
    (bounded_pc_not_sentinel query bounded)

theorem bounded_native_pc_decoded [Fact babyBearModulus.Prime] (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity) (family : PooledFamily)
    (query : Vector (ZMod babyBearModulus) 9)
    (member : query ∈ nativeRows config initial text capacity fits family)
    (bounded : query[0].val < 65536) :
    (nativeDecoderTable (nativeProgramOf config initial text) family).Contains #[] query :=
  native_active_decoded config initial text capacity fits family query member
    (bounded_pc_not_sentinel query bounded)

end Airbender.Trace.NativeDecoder.ProgramRows.Proofs
