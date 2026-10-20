import Airbender.Review.Circuits.SubwordMemory.Decoder
import Airbender.Proofs.SubwordMemory.Values
import Airbender.Proofs.Trace.StatefulDecoderSetup

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification Trace Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}

theorem decoder_field_bounds {instruction : SailRV32.instruction} {data : DecoderData Operation}
    (fields : decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask = data.family.mask ∧ data.funct3 = data.family.funct3 := by
  unfold decoderFields at fields
  split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       exact ⟨Word.ofBitVec_bound _,rfl,rfl⟩)

/-- Native store Booleanity excludes unsupported slots and the whole sentinel tail. -/
theorem padding_excluded
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    decoderQuery w ≠ Vector.replicate 10 (-1) := by
  intro same
  have mask := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) same
  change w 12 = -1 at mask
  rcases store_bit holds with zero | one
  · have impossible : (0 : ZMod mersenne31Modulus) = -1 := zero.symm.trans mask
    exact (by decide +kernel : (0 : ZMod mersenne31Modulus) ≠ -1) impossible
  · have impossible : (1 : ZMod mersenne31Modulus) = -1 := one.symm.trans mask
    exact (by decide +kernel : (1 : ZMod mersenne31Modulus) ≠ -1) impossible

theorem fetched_sources {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧ decoderQuery w = entry.query := by
  obtain ⟨entry,present,same⟩ := sparse_member member (padding_excluded holds)
  exact ⟨entry,present,(run_sparse_setup_sources image present).1,same⟩

theorem entry_fields {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : DecodedFields w entry := by
  have bounds := decoder_field_bounds fields
  have store := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  have funct := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[8]) query
  have zero := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) query
  change w 12 = (entry.data.mask : Nat) at store
  change w 11 = (entry.data.funct3 : Nat) at funct
  change w 8 = (if entry.data.rd = 0 then 1 else 0) at zero
  rw [bounds.2.1] at store
  rw [bounds.2.2] at funct
  exact ⟨store,funct,zero,native_query_indices (by decide) query,
    native_query_pc_word (by decide) query,native_query_immediate_word (by decide) bounds.1 query⟩

theorem fetched_fields {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧ DecodedFields w entry := by
  obtain ⟨entry,present,source,query⟩ := fetched_sources image holds member
  exact ⟨entry,present,source,entry_fields source.fields query⟩

/-- Canonical helper candidate bounds survive the x0 mask derived from decoding. -/
theorem decoded_load_writes {entry : ProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (fields : DecodedFields w entry) (load : w 12 = 0) : DecodedLoadWrites w entry := by
  have candidates : (w 60).val < 65536 ∧ (w 61).val < 65536 := by
    by_cases range : (w 20).val < 64
    · exact (rom_load_values holds load range).2.bounds
    · exact (ram_load_values holds load (by omega)).bounds
  have cases := load_write_cases holds load
  by_cases zero : entry.data.rd = 0
  · have flag : w 8 = 1 := by simpa only [zero,if_true] using fields.zero
    have writes := cases.2 flag
    have low := congrArg (fun q : Vector (ZMod mersenne31Modulus) 2 => q[0]) writes
    have high := congrArg (fun q : Vector (ZMod mersenne31Modulus) 2 => q[1]) writes
    refine ⟨by simpa only [zero,if_true] using writes,?_⟩
    change w 39 = 0 at low
    change w 40 = 0 at high
    simp [Word.Bounded,limbBase,low,high]
  · have flag : w 8 = 0 := by simpa only [zero,if_false] using fields.zero
    have writes := cases.1 flag
    have low := congrArg (fun q : Vector (ZMod mersenne31Modulus) 2 => q[0]) writes
    have high := congrArg (fun q : Vector (ZMod mersenne31Modulus) 2 => q[1]) writes
    refine ⟨by simpa only [zero,if_false] using writes,?_⟩
    change w 39 = w 60 at low
    change w 40 = w 61 at high
    change (w 39).val < 65536 ∧ (w 40).val < 65536
    rwa [low,high]

theorem fetched_load_writes {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (member : setup.table.Contains #[] (decoderQuery w)) (load : w 12 = 0) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      DecodedFields w entry ∧ DecodedLoadWrites w entry := by
  obtain ⟨entry,present,source,fields⟩ := fetched_fields image holds member
  exact ⟨entry,present,source,fields,decoded_load_writes holds fields load⟩

end Airbender.SubwordMemory.Proofs
