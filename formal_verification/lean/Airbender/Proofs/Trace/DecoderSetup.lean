import Airbender.Review.Helpers.Decoder.Setup
import Airbender.Proofs.Trace.Program
import Airbender.Proofs.AddSub.Selectors

namespace Airbender.Trace.Proofs
open Arithmetic

theorem padding_excluded {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      AddSub.importedConstraints) :
    nativeDecoderQuery AddSub.importedConstraintsTraceColumns
      AddSub.importedConstraintsDecoderColumns w ≠ Vector.replicate 10 (-1) := by
  intro same
  have mask := congrArg (fun q : Vector (ZMod p) 10 => q[9]) same
  simp [nativeDecoderQuery, AddSub.importedConstraintsDecoderColumns] at mask
  have small := AddSub.Proofs.packed_mask_bound hp constraints
  have minusOne : (-1 : ZMod p).val = p - 1 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
    exact ZMod.val_neg_one n
  rw [mask, minusOne] at small
  omega

/-- Native equations eliminate the entire padding tail before selecting a row. -/
theorem decoder_member {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {setup : DecoderSetup} {row : Row p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints ()))
    (member : setup.table.Contains #[] row.decoderQuery) :
    ∃ entry ∈ setup.program, row.decoderQuery = entry.query := by
  change ∃ i, row.decoderQuery = setup.row i at member
  obtain ⟨i, same⟩ := member
  unfold DecoderSetup.row at same
  split at same
  · exact ⟨_, List.get_mem _ _, same⟩
  · cases row with
    | mk family w =>
      cases family
      exact (padding_excluded hp constraints same).elim

/-- Public setup construction retains original Sail bytes/decoding evidence. -/
theorem setup_sources {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    {setup : DecoderSetup} (image : decoderSetupImage before count logCapacity = some setup) :
    ∀ entry ∈ setup.program, entry.Source before := by
  unfold decoderSetupImage at image
  split at image
  · cases built : programImage before
        ((List.range count).map fun i => BitVec.ofNat 32 (4 * i)) with
    | none => simp [built] at image
    | some program =>
      simp only [built, bind, Option.bind, pure, Option.some.injEq] at image
      subst setup
      exact program_sources built
  · cases image

theorem decoded_sources {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {trace : Data p} {setup : DecoderSetup} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.Source before ∧ row.decoderQuery = entry.query := by
  intro row member
  obtain ⟨entry, present, same⟩ := decoder_member hp (accepted.constraints row member)
    (decoded row member)
  exact ⟨entry, present, setup_sources image entry present, same⟩

/-- The zero flag is recovered from the selected table row, not assumed per row. -/
theorem decoded_zero_flag {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {trace : Data p} {setup : DecoderSetup}
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (row : Row p) (present : row ∈ trace.rows) :
    row.assignment row.decoderColumns.rdIsZero = 0 ∨
      row.assignment row.decoderColumns.rdIsZero = 1 := by
  obtain ⟨entry, _, same⟩ := decoder_member hp (accepted.constraints row present) (decoded row present)
  have flag := congrArg (fun q : Vector (ZMod p) 10 => q[5]) same
  change row.assignment row.decoderColumns.rdIsZero = (if entry.data.rd = 0 then 1 else 0) at flag
  by_cases zero : entry.data.rd = 0
  · exact Or.inr (by simpa only [zero, if_true] using flag)
  · exact Or.inl (by simpa only [zero, if_false] using flag)

/-- Both decoder-carried words are canonical, from the selected Sail entry. -/
theorem decoded_word_bounds {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} {setup : DecoderSetup} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (row : Row p) (present : row ∈ trace.rows) :
    row.start.word.Bounded ∧ row.decoderImmediate.Bounded := by
  have large : 256 < p := by dsimp [limbBase] at hp; omega
  obtain ⟨entry, _, source, same⟩ := decoded_sources large image accepted decoded row present
  have pc := native_query_pc_word hp same
  have ib := (decoder_field_bounds source.fields).1
  have immediate := native_query_immediate_word hp ib same
  change row.start.word = Word.ofBitVec entry.pc at pc
  change row.decoderImmediate = entry.data.immediate at immediate
  constructor
  · rw [pc]; exact Word.ofBitVec_bound entry.pc
  · rw [immediate]; exact ib

/-- Public setup construction supplies aligned PCs for every real entry. -/
theorem setup_pc_aligned {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    {setup : DecoderSetup} (image : decoderSetupImage before count logCapacity = some setup) :
    ∀ entry ∈ setup.program, (Word.ofBitVec entry.pc).lo % 4 = 0 := by
  unfold decoderSetupImage at image
  split at image
  · cases built : programImage before
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
      obtain ⟨i, _, same⟩ := List.mem_map.mp present
      rw [← same]
      exact indexed_pc_aligned i
  · cases image

/-- Padding exclusion and public setup recover each native incoming alignment. -/
theorem decoded_pc_aligned {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p} {setup : DecoderSetup} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (row : Row p) (present : row ∈ trace.rows) : row.start.word.lo % 4 = 0 := by
  obtain ⟨entry, member, same⟩ := decoder_member (by dsimp [limbBase] at hp; omega)
    (accepted.constraints row present) (decoded row present)
  have canonical := native_query_pc_word hp same
  change row.start.word = Word.ofBitVec entry.pc at canonical
  rw [canonical]
  exact setup_pc_aligned image entry member

end Airbender.Trace.Proofs
