import Airbender.Review.Helpers.Decoder.WordMemorySparse
import Airbender.Proofs.Trace.SparseDecoderSetup
import Airbender.Proofs.Trace.Families.WordMemory.Decoder

namespace Airbender.WordMemory.Proofs
open Trace Airbender.Trace.Proofs

/-- Reuse the actual native mask equation to reject holes and the padding tail. -/
theorem sparse_decoder_member {p : Nat} [Fact p.Prime] (hp : 2 < p)
    {setup : SparseDecoderSetup WordMemoryFamily} {rom : Verification.WordROM}
    {row : Row p WordMemoryFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints rom))
    (member : setup.table.Contains #[] row.decoderQuery) :
    ∃ entry ∈ setup.program, row.decoderQuery = entry.query := by
  apply sparse_member member
  cases row with
  | mk family w => cases family; exact padding_excluded hp constraints

theorem sparse_decoded_sources {p : Nat} [Fact p.Prime] (hp : 2 < p)
    {trace : Data p WordMemoryFamily} {setup : SparseDecoderSetup WordMemoryFamily}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : SparseDecoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query := by
  intro row present
  obtain ⟨entry, member, same⟩ := sparse_decoder_member hp (accepted.constraints row present)
    (decoded row present)
  exact ⟨entry, member, (sparse_setup_sources image member).1, same⟩

/-- Native query equality supplies all canonical decoder inputs; no per-row
    bounds, alignment or zero flag are supplied to the sparse constructor. -/
theorem sparse_decoded_inputs {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {trace : Data p WordMemoryFamily} {setup : SparseDecoderSetup WordMemoryFamily}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : SparseDecoded trace setup)
    (row : Row p WordMemoryFamily) (present : row ∈ trace.rows) :
    row.start.word.Bounded ∧ row.decoderImmediate.Bounded ∧ row.start.word.lo % 4 = 0 ∧
      row.assignment row.decoderColumns.rdIsZero =
        if (row.assignment row.decoderColumns.rd).val = 0 then 1 else 0 := by
  obtain ⟨entry, member, source, same⟩ := sparse_decoded_sources
    (by dsimp [Arithmetic.limbBase] at hp; omega) image accepted decoded row present
  have pc := native_query_pc_word hp same
  change row.start.word = Arithmetic.Word.ofBitVec entry.pc at pc
  have immediateBound := (decoder_field_bounds source.fields).1
  have immediate := native_query_immediate_word hp immediateBound same
  change row.decoderImmediate = entry.data.immediate at immediate
  have rd := (native_query_indices hp same).2.2
  have flag := congrArg (fun q : Vector (ZMod p) 10 => q[5]) same
  change row.assignment row.decoderColumns.rdIsZero = (if entry.data.rd = 0 then 1 else 0) at flag
  have zero : entry.data.rd = 0 ↔ entry.data.rd.toNat = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; exact BitVec.eq_of_toNat_eq (by simpa using h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pc]; exact Arithmetic.Word.ofBitVec_bound _
  · rw [immediate]; exact immediateBound
  · rw [pc]; exact (sparse_setup_sources image member).2.2
  · rw [rd]; simpa only [zero] using flag

end Airbender.WordMemory.Proofs
