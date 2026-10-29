import Airbender.Review.Helpers.Decoder.UnifiedProgramRows
import Airbender.Proofs.GKRProtocol.ProgramRows

namespace Airbender.Trace.NativeDecoder.UnifiedProgramRows.Proofs
open Airbender.Trace.NativeDecoder.UnifiedProgramRows
open Airbender.Trace.NativeDecoder.ProgramRows

theorem rows_length {p : Nat} (initial : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (capacity : Nat) (fits : text.length ≤ capacity) :
    (rows (p := p) initial text capacity fits).length = capacity := by
  simp [rows]
  omega

/-- Each noncaller entry accepted by the unified public-text model is the
actual pure Sail decode of the supplied bytes at its indexed PC. -/
theorem ordinary_sources (initial : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (image : ROM.TextImage initial text)
    (size : text.length ≤ ROM.limit / 4) :
    ∀ ordinary ∈ ordinaryProgramOf initial text,
      ordinary.SourceWith initial decoderFields := by
  intro ordinary member
  obtain ⟨item, inProgram, selected⟩ := List.mem_filterMap.mp member
  cases item with
  | inr caller => simp [ordinaryProgramOf] at selected
  | inl decodedEntry =>
    have equal : decodedEntry = ordinary := by simpa using selected
    subst ordinary
    obtain ⟨⟨bits, index⟩, inText, source⟩ := List.mem_filterMap.mp inProgram
    have found : text[index]? = some bits := List.mk_mem_zipIdx_iff_getElem?.mp inText
    have indexBound : index < text.length := by
      by_contra notBound
      have : text[index]? = none := by simp [Nat.le_of_not_gt notBound]
      rw [this] at found
      contradiction
    have value : text[index] = bits := by
      have : text[index]? = some text[index] := by simp [indexBound]
      rw [this] at found
      exact Option.some.inj found
    have bytes : (Trace.Cell.ram (BitVec.ofNat 32 (4 * index))).read initial =
        .ok bits initial := by
      simpa only [value] using ROM.Proofs.bytes_of_text_image initial text image size
        ⟨index, indexBound⟩
    unfold entry at source
    cases caller : callerEntryWith delegationCSR initial bits index with
    | some found => simp [caller] at source
    | none =>
      cases decoded : SailRV32.Functions.encdec_backwards bits with
      | impure call continuation => simp [caller, decoded] at source
      | pure instruction =>
        cases fields : decoderFields instruction with
        | none => simp [caller, decoded, fields] at source
        | some data =>
          simp only [caller, decoded, fields, bind, Option.bind] at source
          change (some (Sum.inl ⟨BitVec.ofNat 32 (4 * index), bits,
            instruction, data⟩) : Option Entry) = some (Sum.inl decodedEntry) at source
          cases source
          exact ⟨bytes, by rw [decoded]; rfl, fields⟩

/-- The public ordinary unified program can be reconstructed by stateful Sail
reads. The virtual CSR callers are checked by their separate registry. -/
theorem ordinary_program_image (initial : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (image : ROM.TextImage initial text)
    (size : text.length ≤ ROM.limit / 4) :
    programImageRunWith decoderFields initial
      ((ordinaryProgramOf initial text).map ProgramEntry.pc) =
        some (ordinaryProgramOf initial text) :=
  Airbender.Compiler.PublicProgram.image_run _
    (ordinary_sources initial text image size)

theorem active_member {p : Nat} (initial : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (capacity : Nat) (fits : text.length ≤ capacity)
    (query : Vector (ZMod p) 9)
    (member : query ∈ rows initial text capacity fits)
    (active : query ≠ sentinel) :
    ∃ item ∈ programOf initial text, query = item.query := by
  rcases List.mem_append.mp member with source | padding
  · rcases List.mem_map.mp source with ⟨pair, inText, rowEq⟩
    rcases pair with ⟨bits, index⟩
    cases entryEq : entry initial bits index with
    | none =>
        have hs : query = sentinel := by simpa [wordRow, entryEq] using rowEq.symm
        exact (active hs).elim
    | some item =>
        have inProgram : item ∈ programOf initial text := by
          exact List.mem_filterMap.mpr ⟨(bits, index), inText, entryEq⟩
        have hq : query = item.query := by
          simpa [wordRow, entryEq] using rowEq.symm
        exact ⟨item, inProgram, hq⟩
  · have hs : query = sentinel := (List.mem_replicate.mp padding).2
    exact (active hs).elim

theorem active_decoded {p : Nat} [Fact p.Prime]
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity) (query : Vector (ZMod p) 9)
    (member : query ∈ rows initial text capacity fits)
    (active : query ≠ sentinel) :
    (decoderTable (programOf initial text)).Contains #[] query := by
  obtain ⟨item, inProgram, hq⟩ :=
    active_member initial text capacity fits query member active
  apply (decoderTable (programOf initial text)).implied_by_completeness #[] query
  change ∃ item ∈ programOf initial text, query = item.query
  exact ⟨item, inProgram, hq⟩

theorem bounded_pc_decoded [Fact babyBearModulus.Prime]
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (fits : text.length ≤ capacity)
    (query : Vector (ZMod babyBearModulus) 9)
    (member : query ∈ rows initial text capacity fits)
    (bounded : query[0].val < 65536) :
    (decoderTable (programOf initial text)).Contains #[] query :=
  active_decoded initial text capacity fits query member
    (ProgramRows.Proofs.bounded_pc_not_sentinel query bounded)

end Airbender.Trace.NativeDecoder.UnifiedProgramRows.Proofs
