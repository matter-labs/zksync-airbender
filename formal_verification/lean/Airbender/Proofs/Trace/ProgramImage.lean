import Airbender.Review.Helpers.Decoder.ArithmeticSparse
import Airbender.Proofs.Trace.DecoderSetup
import Airbender.Proofs.Trace.SparseDecoderSetup

namespace Airbender.Trace.Proofs
open Arithmetic Trace Reference.RiscV.Sail
open AddSub

/-- Arithmetic packed-mask bounds reject unsupported interior slots and tail. -/
theorem sparse_decoder_member {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {setup : SparseDecoderSetup Family} {row : Row p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints ()))
    (member : setup.table.Contains #[] row.decoderQuery) :
    ∃ entry ∈ setup.program, row.decoderQuery = entry.query := by
  apply sparse_member member
  cases row with
  | mk family w => cases family; exact padding_excluded hp constraints

/-- Internal construction evidence shared by strict and sparse public builders.
    Each selected entry retains its actual indexed PC, bytes and pure decoder.
    This is derived in Proofs; no public execution theorem assumes it. -/
structure IndexedProgram (before : State) (count : Nat)
    (program : List (ProgramEntry)) : Prop where
  locations : ∀ entry ∈ program, ∃ i < count, entry.pc = BitVec.ofNat 32 (4 * i)
  sources : ∀ entry ∈ program, entry.SourceWith before decoderFields
  pureDecoders : ∀ entry ∈ program,
    SailRV32.Functions.encdec_backwards entry.bits = .pure entry.instruction

theorem strict_indexed_program {before : State} {count logCapacity : Nat} {setup : DecoderSetup}
    (image : decoderSetupImage before count logCapacity = some setup) :
    IndexedProgram before count setup.program := by
  refine ⟨?_, setup_sources image, setup_decoders_pure image⟩
  unfold decoderSetupImage at image
  split at image
  · cases built : programImageWith decoderFields before
        ((List.range count).map fun i => BitVec.ofNat 32 (4 * i)) with
    | none => simp [built] at image
    | some program =>
      simp only [built, bind, Option.bind, pure, Option.some.injEq] at image
      subst setup
      intro entry member
      have addresses := program_addresses built
      have present : entry.pc ∈ (List.range count).map (fun i => BitVec.ofNat 32 (4 * i)) := by
        rw [← addresses]
        exact List.mem_map.mpr ⟨entry, member, rfl⟩
      obtain ⟨i, bound, same⟩ := List.mem_map.mp present
      exact ⟨i, List.mem_range.mp bound, same.symm⟩
  · cases image

theorem sparse_indexed_program {before : State} {count logCapacity : Nat}
    {setup : SparseDecoderSetup Family}
    (image : sparseDecoderSetupImage before count logCapacity = some setup) :
    IndexedProgram before count setup.program := by
  constructor
  · intro entry member
    obtain ⟨i, bound, built⟩ := sparse_setup_selected image member
    exact ⟨i, bound, (entry_source built).1⟩
  · intro entry member
    exact (sparse_setup_sources image member).1
  · intro entry member
    exact (sparse_setup_sources image member).2.1

theorem IndexedProgram.pc_aligned {before : State} {count : Nat}
    {program : List (ProgramEntry)} (image : IndexedProgram before count program)
    {entry : ProgramEntry} (member : entry ∈ program) :
    (Word.ofBitVec entry.pc).lo % 4 = 0 := by
  obtain ⟨i, _, same⟩ := image.locations entry member
  rw [same]
  exact indexed_pc_aligned i

/-- Retained entry membership is only an internal finite selection index. The
    sparse physical table, holes and original PCs remain unchanged. -/
def selectedSetup (setup : SparseDecoderSetup Family) : DecoderSetup :=
  ⟨setup.program, 0⟩

theorem sparse_selected_decoded {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {trace : Data p} {setup : SparseDecoderSetup Family}
    (accepted : Accepted trace) (decoded : SparseDecoded trace setup) :
    Decoded trace (selectedSetup setup) := by
  intro row present
  obtain ⟨entry, member, same⟩ := sparse_decoder_member hp (accepted.constraints row present)
    (decoded row present)
  obtain ⟨i, bound, selected⟩ := List.mem_iff_getElem.mp member
  change ∃ j : Fin (setup.program.length + 0), row.decoderQuery = (selectedSetup setup).row j
  refine ⟨⟨i, by omega⟩, ?_⟩
  simpa [DecoderSetup.row, selectedSetup, bound, selected] using same

/-- Canonical words and indexed alignment follow from construction and accepted
    complete membership, independently of the public builder's slot representation. -/
theorem indexed_decoder_inputs {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} {setup : DecoderSetup} {before : State} {count : Nat}
    (image : IndexedProgram before count setup.program)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (row : Row p) (present : row ∈ trace.rows) :
    row.start.word.Bounded ∧ row.decoderImmediate.Bounded ∧ row.start.word.lo % 4 = 0 := by
  obtain ⟨entry, member, same⟩ := decoder_member (by dsimp [limbBase] at hp; omega)
    (accepted.constraints row present) (decoded row present)
  have pc := native_query_pc_word hp same
  change row.start.word = Word.ofBitVec entry.pc at pc
  have immediateBound := (decoder_field_bounds (image.sources entry member).fields).1
  have immediate := native_query_immediate_word hp immediateBound same
  change row.decoderImmediate = entry.data.immediate at immediate
  rw [pc, immediate]
  exact ⟨Word.ofBitVec_bound _, immediateBound, image.pc_aligned member⟩

end Airbender.Trace.Proofs
