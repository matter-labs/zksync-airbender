import Airbender.Proofs.Sail.Decoder
import Airbender.Review.Circuits.JumpBranchSlt.Decoder
import Airbender.Proofs.Trace.SparseDecoderSetup
import Airbender.Proofs.JumpBranchSlt.PC

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace
open Airbender.Trace.Proofs

/-- Original instruction metadata supplies bounds and the supported native mask. -/
theorem decoder_field_bounds {instruction : SailRV32.instruction}
    {data : DecoderData Unit} (fields : decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask ∈ [1, 2, 4, 8, 16] ∧ data.funct3 < 8 := by
  unfold decoderFields at fields
  split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       constructor
       · first | exact Word.ofBitVec_bound _ | (simp [Word.Bounded, limbBase])
       · constructor
         · dsimp; decide
         · dsimp
           first | decide | exact Nat.mod_lt _ (by decide) |
             (rename_i op; cases op <;> decide))

/-- Native mask equations reject unsupported slots and the entire sentinel tail. -/
theorem padding_excluded {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    decoderQuery w ≠ Vector.replicate 10 (-1) := by
  intro same
  have mask := congrArg (fun q : Vector (ZMod p) 10 => q[9]) same
  simp [decoderQuery, nativeDecoderQuery, importedConstraintsDecoderColumns] at mask
  have small := packed_mask_bound hp constraints
  have minusOne : (-1 : ZMod p).val = p - 1 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
    exact ZMod.val_neg_one n
  rw [mask, minusOne] at small
  omega

theorem decoder_member {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {setup : SparseDecoderSetup Unit} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, decoderQuery w = entry.query :=
  sparse_member member (padding_excluded hp constraints)

/-- Successful public construction derives actual bytes and original Sail decoding. -/
theorem fetched_sources {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {w : Nat → ZMod p} {setup : SparseDecoderSetup Unit}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧ decoderQuery w = entry.query := by
  obtain ⟨entry, present, same⟩ := decoder_member hp constraints member
  exact ⟨entry, present, (sparse_setup_sources image present).1, same⟩

theorem query_mask {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {w : Nat → ZMod p} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : (w 12).val ∈ [1, 2, 4, 8, 16] := by
  have mask := (decoder_field_bounds fields).2.1
  have bound : entry.data.mask < p := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at mask
    omega
  have same := congrArg (fun q : Vector (ZMod p) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod p) at same
  rwa [same, ZMod.val_natCast_of_lt bound]

/-- Canonical raw funct3 is recovered from the same native lookup column. -/
theorem query_tag {p : Nat} [Fact p.Prime] (hp : 8 < p)
    {w : Nat → ZMod p} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : (w 11).val = entry.data.funct3 := by
  have bound := (decoder_field_bounds fields).2.2
  have same := congrArg (fun q : Vector (ZMod p) 10 => q[8]) query
  change w 11 = (entry.data.funct3 : ZMod p) at same
  rw [same, ZMod.val_natCast_of_lt (lt_trans bound hp)]

/-- Exact native query columns derive both canonical words and the x0 flag. -/
theorem query_inputs {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {w : Nat → ZMod p} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    (⟨(w 0).val, (w 1).val⟩ : Word).Bounded ∧
    (⟨(w 9).val, (w 10).val⟩ : Word).Bounded ∧
    w 8 = if (w 7).val = 0 then 1 else 0 := by
  have pc := native_query_pc_word hp query
  have immediateBound := (decoder_field_bounds fields).1
  have immediate := native_query_immediate_word hp immediateBound query
  change (⟨(w 0).val, (w 1).val⟩ : Word) = Word.ofBitVec entry.pc at pc
  change (⟨(w 9).val, (w 10).val⟩ : Word) = entry.data.immediate at immediate
  have rd := (native_query_indices hp query).2.2
  change (w 7).val = entry.data.rd.toNat at rd
  have flag := congrArg (fun q : Vector (ZMod p) 10 => q[5]) query
  change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
  have zero : entry.data.rd = 0 ↔ entry.data.rd.toNat = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; exact BitVec.eq_of_toNat_eq (by simpa using h)
  refine ⟨by rw [pc]; exact Word.ofBitVec_bound _, by rw [immediate]; exact immediateBound, ?_⟩
  rw [rd]
  simpa only [zero] using flag

theorem decoded_inputs {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {w : Nat → ZMod p} {setup : SparseDecoderSetup Unit}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    (⟨(w 0).val, (w 1).val⟩ : Word).Bounded ∧ (w 0).val % 4 = 0 ∧
    (⟨(w 9).val, (w 10).val⟩ : Word).Bounded ∧
    w 8 = if (w 7).val = 0 then 1 else 0 := by
  obtain ⟨entry, present, source, same⟩ := fetched_sources
    (by dsimp [limbBase] at hp; omega) image constraints member
  obtain ⟨pcBound, immBound, flag⟩ := query_inputs hp source.fields same
  have pc := native_query_pc_word hp same
  change (⟨(w 0).val, (w 1).val⟩ : Word) = Word.ofBitVec entry.pc at pc
  have low := congrArg Word.lo pc
  change (w 0).val = (Word.ofBitVec entry.pc).lo at low
  exact ⟨pcBound, by rw [low]; exact (sparse_setup_sources image present).2.2, immBound, flag⟩

theorem public_decoder {w : Nat → ZMod mersenne31Modulus} {setup : SparseDecoderSetup Unit}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    Fetched w before ∧ (w 13).val < 65536 ∧ (w 14).val < 65536 := by
  obtain ⟨entry, _, source, same⟩ := fetched_sources (by decide) image constraints member
  exact ⟨⟨entry, source, same⟩, pc_bounds constraints (query_mask (by decide) source.fields same)⟩

/-- JAL and branch parity is derived from the actual Sail decoder and the
    metadata's sign extension, rather than supplied as a row assumption. -/
theorem decoder_offset_even {before : Reference.RiscV.Sail.State} {entry : ProgramEntry}
    (source : entry.SourceWith before decoderFields) :
    match entry.instruction with
    | .JAL _ | .BTYPE _ => entry.data.immediate.lo % 2 = 0
    | _ => True := by
  have decoded := Reference.Sail.decoded_offset_even entry.bits before entry.instruction before
    source.decoded
  have fields := source.fields
  cases kind : entry.instruction
  case JAL args =>
    rcases args with ⟨imm, rd⟩
    cases rd with
    | Regidx bits =>
      rw [kind] at fields decoded
      simp only [decoderFields] at fields
      rw [← Option.some.inj fields]
      exact Reference.Sail.sign_extend_low_even (by decide) imm decoded
  case BTYPE args =>
    rcases args with ⟨imm, rs2, rs1, op⟩
    cases rs2 with
    | Regidx right =>
      cases rs1 with
      | Regidx left =>
        rw [kind] at fields decoded
        simp only [decoderFields, Option.some.injEq] at fields
        rw [← fields]
        exact Reference.Sail.sign_extend_low_even (by decide) imm decoded
  all_goals trivial

/-- Full native query membership connects direct-offset parity to the original
    successful Sail decode; it is not supplied by the row caller. -/
theorem direct_offset_even {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    {before : Reference.RiscV.Sail.State}
    (source : entry.SourceWith before decoderFields) (query : decoderQuery w = entry.query)
    (mask : (w 12).val = 1) : (w 9).val % 2 = 0 := by
  have fieldBounds := decoder_field_bounds source.fields
  have small : entry.data.mask < mersenne31Modulus := by
    have cases := fieldBounds.2.1
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at cases
    rcases cases with eq | eq | eq | eq | eq <;> rw [eq] <;> decide
  have packed := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at packed
  have one : entry.data.mask = 1 := by
    rw [packed, ZMod.val_natCast_of_lt small] at mask
    exact mask
  have immediate := Trace.Proofs.native_query_immediate_word (by decide) fieldBounds.1 query
  change (Word.mk (w 9).val (w 10).val) = entry.data.immediate at immediate
  have low := congrArg Word.lo immediate
  change (w 9).val = entry.data.immediate.lo at low
  rw [low]
  have parity := decoder_offset_even source
  have fields := source.fields
  unfold decoderFields at fields
  split at fields
  all_goals first
    | cases fields
    | (rw [← Option.some.inj fields] at one ⊢; simp_all)
  all_goals simpa only [← fields] using parity

end Airbender.JumpBranchSlt.Proofs
