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
