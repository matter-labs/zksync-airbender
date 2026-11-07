import Airbender.Review.Circuits.ReducedMachine.JumpDecoder
import Airbender.Proofs.ReducedMachine.NativeShiftDecoder
import Airbender.Proofs.Sail.Decoder

namespace Airbender.ReducedMachine.NativeJumpDecoderProofs
open Arithmetic Trace Native
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The retained original forms determine bounded immediate, exact native mask
    and bounded raw funct3, including raw JAL bits. -/
theorem field_bounds {instruction : SailRV32.instruction} {data : DecoderData JumpMode}
    (fields : jumpDecoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask = jumpMask data.family ∧ data.funct3 < 8 := by
  unfold jumpDecoderFields at fields
  split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       refine ⟨Word.ofBitVec_bound _,rfl,?_⟩
       first | exact Nat.mod_lt _ (by decide) | (change 0 < 8; decide))

/-- Complete sparse/padded membership recovers original public Sail sources;
    accepted native Boolean packing excludes holes and the all-minus-one tail. -/
theorem fetched_sources {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup JumpMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat} {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    (image : jumpDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before jumpDecoderFields ∧ decoderQuery w = entry.query := by
  obtain ⟨entry,present,same⟩ := sparse_member member (NativeShiftDecoderProofs.padding_excluded holds)
  exact ⟨entry,present,(run_sparse_setup_sources image present).1,same⟩

/-- No per-row mask, source index, zero flag, immediate or funct3 answer is supplied. -/
theorem decoded_fields {w : Nat → ZMod mersenne31Modulus} {entry : JumpProgramEntry}
    (fields : jumpDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : JumpDecoded w entry := by
  have mask := (field_bounds fields).2.1
  have q (slot : Fin 10) := congrArg (fun v : Vector (ZMod mersenne31Modulus) 10 => v[slot]) query
  refine ⟨?_,q 2,q 3,q 4,q 5,?_,q 8⟩
  · have same := q 9
    change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at same
    simpa only [mask] using same
  · exact congrArg₂ (fun a b : ZMod mersenne31Modulus => #v[a,b]) (q 6) (q 7)

/-- Canonical native immediate words follow from original decoded bounds, not
    a supplied native field range or expected result. -/
theorem immediate_word {w : Nat → ZMod mersenne31Modulus} {entry : JumpProgramEntry}
    (fields : jumpDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : jumpImmediateWord w = entry.data.immediate := by
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

/-- Original Sail decoding derives even direct offsets. JALR is not filtered. -/
theorem offset_even {before : Reference.RiscV.Sail.State} {entry : JumpProgramEntry}
    (source : entry.SourceWith before jumpDecoderFields) (direct : entry.data.family = true) :
    entry.data.immediate.lo % 2 = 0 := by
  have decoded := Reference.Sail.decoded_offset_even entry.bits before entry.instruction before source.decoded
  have fields := source.fields
  cases kind : entry.instruction
  case JAL args =>
    rcases args with ⟨imm,rd⟩
    cases rd with
    | Regidx index =>
      rw [kind] at fields decoded
      simp only [jumpDecoderFields,Option.some.injEq] at fields
      rw [← fields]
      exact Reference.Sail.sign_extend_low_even (by decide) imm decoded
  case JALR args =>
    rcases args with ⟨imm,rs1,rd⟩
    cases rs1 with
    | Regidx left =>
      cases rd with
      | Regidx index =>
        rw [kind] at fields
        simp only [jumpDecoderFields,Option.some.injEq] at fields
        rw [← fields] at direct
        cases direct
  all_goals simp [jumpDecoderFields,kind] at fields

end Airbender.ReducedMachine.NativeJumpDecoderProofs
