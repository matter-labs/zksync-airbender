import Airbender.Review.Helpers.Decoder.ProgramRows
import Airbender.Review.Helpers.Delegation.SplitCaller

namespace Airbender.Keccak.Split.Caller.Proofs
open Airbender.Keccak.Split
open Airbender.Trace.NativeDecoder.ProgramRows
set_option warningAsError true

/-- The three blessed CSR addresses have a unique split worker kind. -/
theorem kind_of_csr (kind : Kind) : kindOfCSR kind.csr = some kind := by
  cases kind <;> decide

theorem kind_of_csr_sound {address : Nat} {kind : Kind}
    (selected : kindOfCSR address = some kind) : address = kind.csr := by
  unfold kindOfCSR at selected
  split at selected
  · cases selected
    simp_all [Kind.csr]
  · split at selected
    · cases selected
      simp_all [Kind.csr]
    · split at selected
      · cases selected
        simp_all [Kind.csr]
      · simp at selected

/-- Full unsigned preprocessing accepts all three split forms; reduced
preprocessing accepts none of them. -/
theorem full_unsigned_allows_split (kind : Kind) :
    Config.fullUnsigned.delegationCSR kind.csr = true := by
  cases kind <;> decide

theorem reduced_excludes_split (kind : Kind) :
    Config.reduced.delegationCSR kind.csr = false := by
  cases kind <;> decide

/-- Every word of a blessed public group selects its intended split worker
and is admitted by the full unsigned native preprocessing allowlist. The
separate worker/control proof must still establish its functional effect. -/
theorem blessed_group_admitted (text : List (BitVec 32)) (index : Nat)
    (group : SplitCallGroup text index) :
    ∃ start, start ≤ index ∧ index < start + 361 ∧
      ∀ offset < 361,
        text[start + offset]? = some (csrWord (kindAt offset).csr) ∧
        kindOfCSR (kindAt offset).csr = some (kindAt offset) ∧
        Config.fullUnsigned.delegationCSR (kindAt offset).csr = true := by
  obtain ⟨start, begins, ends, words⟩ := group
  exact ⟨start, begins, ends, fun offset bound =>
    ⟨words offset bound, kind_of_csr _, full_unsigned_allows_split _⟩⟩

/-- Preserve the public PC, instruction and bits when interpreting a native
virtual caller as a split-worker caller. -/
def fromNative (caller : CallerEntry) (kind : Kind) : ProgramEntry :=
  ⟨caller.pc, caller.bits, caller.instruction,
    ⟨kind, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩⟩

/-- The split-worker lookup query is exactly the full-width native CSR query.
No truncated register-index interpretation is used. -/
theorem query_from_native {p : Nat} (caller : CallerEntry) (kind : Kind)
    (selected : kindOfCSR caller.csr = some kind) :
    query (p := p) (fromNative caller kind) = caller.query := by
  have csr := kind_of_csr_sound selected
  simp [query, fromNative, CallerEntry.query, csr]

/-- A caller from public bytes and pure Sail decoding remains sourced after
projection into the split registry. This supplies metadata, not worker effects. -/
theorem source_of_native (before : Reference.RiscV.Sail.State)
    (caller : CallerEntry) (kind : Kind)
    (source : caller.Source before Config.fullUnsigned.delegationCSR)
    (selected : kindOfCSR caller.csr = some kind) :
    (fromNative caller kind).SourceWith before decoderFields := by
  refine ⟨source.bytes, source.decoded, ?_⟩
  obtain ⟨address, shape, csr⟩ := source.csrShape
  rw [csr] at selected
  change decoderFields caller.instruction = some ⟨kind, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  rw [shape]
  simp [decoderFields, selected]

/-- A split caller projected from the public native program is present in
the modeled add/sub decoder table with its complete CSR query. Exact matching
to an actual compiled lookup remains an explicit boundary premise. -/
theorem modeled_split_member {p : Nat} [Fact p.Prime]
    (program : List NativeEntry) (caller : CallerEntry) (kind : Kind)
    (member : Sum.inr caller ∈ program)
    (selected : kindOfCSR caller.csr = some kind) :
    (nativeDecoderTable (p := p) program .addSub).Contains #[]
      (query (p := p) (fromNative caller kind)) := by
  apply (nativeDecoderTable (p := p) program .addSub).implied_by_completeness
  change ∃ entry ∈ program, entry.family = .addSub ∧
    query (p := p) (fromNative caller kind) = entry.query
  exact ⟨.inr caller, member, rfl, query_from_native caller kind selected⟩

end Airbender.Keccak.Split.Caller.Proofs
