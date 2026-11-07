import Airbender.Review.Circuits.ReducedMachine.CSRDecoder
import Airbender.Proofs.ReducedMachine.NativeShiftDecoder

namespace Airbender.ReducedMachine.NativeCSRDecoderProofs
open Arithmetic Trace Native
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Recover the original constructor and its exact unsigned CSR metadata. -/
theorem original_fields {instruction : SailRV32.instruction} {data : DecoderData CSRMode}
    (fields : csrDecoderFields instruction = some data) :
    ∃ index : BitVec 12, ∃ rs1 rd : BitVec 5,
      instruction = .CSRReg (index,.Regidx rs1,.Regidx rd,.CSRRW) ∧
      data = ⟨(),rs1,0,rd,⟨index.toNat,0⟩,csrMask,1⟩ := by
  unfold csrDecoderFields at fields
  split at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       exact ⟨_,_,_,rfl,fields.symm⟩)

/-- CSR indices are unsigned, not sign-extended; unused rs2 is exactly x0. -/
theorem field_bounds {instruction : SailRV32.instruction} {data : DecoderData CSRMode}
    (fields : csrDecoderFields instruction = some data) :
    data.immediate.lo < 4096 ∧ data.immediate.hi = 0 ∧ data.rs2 = 0 ∧
      data.mask = csrMask ∧ data.funct3 = 1 := by
  obtain ⟨index,rs1,rd,rfl,rfl⟩ := original_fields fields
  exact ⟨index.isLt,rfl,rfl,rfl,rfl⟩

/-- Full sparse/padded membership recovers actual original public sources;
    native Boolean packing rejects unsupported holes and all-minus-one tail. -/
theorem fetched_sources {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup CSRMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat} {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    (image : csrDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before csrDecoderFields ∧ decoderQuery w = entry.query := by
  obtain ⟨entry,present,same⟩ := sparse_member member (NativeShiftDecoderProofs.padding_excluded holds)
  exact ⟨entry,present,(run_sparse_setup_sources image present).1,same⟩

/-- Native query identity supplies every CSR selector/operand/rd/x0 field. -/
theorem decoded_fields {w : Nat → ZMod mersenne31Modulus} {entry : CSRProgramEntry}
    (fields : csrDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : CSRDecoded w entry := by
  have bounds := field_bounds fields
  have q (slot : Fin 10) := congrArg (fun v : Vector (ZMod mersenne31Modulus) 10 => v[slot]) query
  refine ⟨?_,q 2,?_,q 4,q 5,?_,?_⟩
  · have same := q 9
    change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at same
    simpa only [bounds.2.2.2.1] using same
  · have same := q 3
    change w 6 = (entry.data.rs2.toNat : ZMod mersenne31Modulus) at same
    rw [bounds.2.2.1] at same
    exact same
  · have high := q 7
    change w 10 = (entry.data.immediate.hi : ZMod mersenne31Modulus) at high
    rw [bounds.2.1,Nat.cast_zero] at high
    exact congrArg₂ (fun a b : ZMod mersenne31Modulus => #v[a,b]) (q 6) high
  · have same := q 8
    change w 11 = (entry.data.funct3 : ZMod mersenne31Modulus) at same
    simpa [bounds.2.2.2.2] using same

/-- Canonical native key bound and zero upper limb follow the original source,
    independently of any chosen CSR allow-list or caller source value. -/
theorem key_bounds {w : Nat → ZMod mersenne31Modulus} {entry : CSRProgramEntry}
    (fields : csrDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : (w 9).val < 4096 ∧ w 10 = 0 := by
  have decoded := decoded_fields fields query
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) decoded.immediate
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) decoded.immediate
  change w 9 = (entry.data.immediate.lo : ZMod mersenne31Modulus) at low
  change w 10 = 0 at high
  have bound := (field_bounds fields).1
  have small : 4096 < mersenne31Modulus := by decide
  exact ⟨by rw [low,ZMod.val_natCast_of_lt (lt_trans bound small)]; exact bound,high⟩
end Airbender.ReducedMachine.NativeCSRDecoderProofs
