import Airbender.Review.Circuits.ReducedMachine.BranchDecoder
import Airbender.Proofs.ReducedMachine.NativeShiftDecoder
import Airbender.Proofs.Sail.Decoder

namespace Airbender.ReducedMachine.NativeBranchDecoderProofs
open Arithmetic Trace Native
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem tags (op : BranchMode) : branchFunct3 op ∈ [0,1,4,5,6,7] := by
  cases op <;> decide

/-- Original constructors determine canonical offset, exact mask/tag and dummy rd. -/
theorem field_bounds {instruction : SailRV32.instruction} {data : DecoderData BranchMode}
    (fields : branchDecoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask = branchMask ∧ data.rd = 0 ∧
      data.funct3 = branchFunct3 data.family := by
  unfold branchDecoderFields at fields
  split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       exact ⟨Word.ofBitVec_bound _,rfl,rfl,rfl⟩)

/-- Complete sparse/padded membership recovers original public Sail sources;
    accepted native Boolean packing excludes holes and the all-minus-one tail. -/
theorem fetched_sources {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup BranchMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat} {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    (image : branchDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before branchDecoderFields ∧ decoderQuery w = entry.query := by
  obtain ⟨entry,present,same⟩ := sparse_member member (NativeShiftDecoderProofs.padding_excluded holds)
  exact ⟨entry,present,(run_sparse_setup_sources image present).1,same⟩


/-- Every actual ten-field query binding is recovered from original fields. -/
theorem decoded_fields {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry}
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : BranchDecoded w entry := by
  have bounds := field_bounds fields
  have q (slot : Fin 10) := congrArg (fun v : Vector (ZMod mersenne31Modulus) 10 => v[slot]) query
  refine ⟨?_,q 2,q 3,?_,?_,?_,?_⟩
  · have same := q 9
    change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at same
    simpa only [bounds.2.1] using same
  · have same := q 4
    change rdIndex w = (entry.data.rd.toNat : ZMod mersenne31Modulus) at same
    simpa [bounds.2.2.1] using same
  · have same := q 5
    change rdZeroFlag w = (if entry.data.rd = 0 then 1 else 0) at same
    simpa [bounds.2.2.1] using same
  · exact congrArg₂ (fun a b : ZMod mersenne31Modulus => #v[a,b]) (q 6) (q 7)
  · have same := q 8
    change w 11 = (entry.data.funct3 : ZMod mersenne31Modulus) at same
    simpa only [bounds.2.2.2] using same

/-- Canonical actual offset limbs follow from original sign extension. -/
theorem immediate_word {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry}
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : branchOffsetWord w = entry.data.immediate := by
  have decoded := decoded_fields fields query
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) decoded.immediate
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) decoded.immediate
  change w 9 = (entry.data.immediate.lo : ZMod mersenne31Modulus) at low
  change w 10 = (entry.data.immediate.hi : ZMod mersenne31Modulus) at high
  have bounds := (field_bounds fields).1
  have small : limbBase < mersenne31Modulus := by decide
  apply congrArg₂ Word.mk
  · rw [low,ZMod.val_natCast_of_lt (lt_trans bounds.1 small)]
  · rw [high,ZMod.val_natCast_of_lt (lt_trans bounds.2 small)]

/-- Offset parity is derived from the retained original Sail decoder, not a
    public per-row even-offset answer or a filtered BTYPE constructor. -/
theorem offset_even {before : Reference.RiscV.Sail.State} {entry : BranchProgramEntry}
    (source : entry.SourceWith before branchDecoderFields) : entry.data.immediate.lo % 2 = 0 := by
  have decoded := Reference.Sail.decoded_offset_even entry.bits before entry.instruction before source.decoded
  have fields := source.fields
  cases kind : entry.instruction
  case BTYPE args =>
    rcases args with ⟨imm,rs2,rs1,op⟩
    cases rs2 with
    | Regidx right =>
      cases rs1 with
      | Regidx left =>
        rw [kind] at fields decoded
        simp only [branchDecoderFields,Option.some.injEq] at fields
        rw [← fields]
        exact Reference.Sail.sign_extend_low_even (by decide) imm decoded
  all_goals simp [branchDecoderFields,kind] at fields

end Airbender.ReducedMachine.NativeBranchDecoderProofs
