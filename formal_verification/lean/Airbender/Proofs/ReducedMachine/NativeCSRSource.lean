import Airbender.Review.Helpers.Memory.ReducedMachineCSRRequests
import Airbender.Proofs.ReducedMachine.NativeCSRPorts
import Airbender.Proofs.ReducedMachine.NativeRuntimeCSRResult
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.ReducedMachine.NativeCSRSourceProofs
open Native Arithmetic Verification Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Bounded actual limbs recover the original architectural source exactly,
    including full RV32 values above the Mersenne31 modulus. -/
theorem source_word {w : Nat → ZMod mersenne31Modulus} {entry : CSRProgramEntry}
    {before after : State}
    (transfer : CSRRegisterTransfer (.mk .reduced w) entry before after)
    (bounded : (sourceWord w).Bounded) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
        .ok (sourceWord w).toBitVec before ∧
      (sourceWord w).toBitVec.toNat = (sourceWord w).value ∧
      sourceWord w = Word.ofBitVec (sourceWord w).toBitVec := by
  have read := transfer.1 0
  have original : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (sourceWord w).toBitVec before := by
    simpa [memoryWord,MemoryPort.readCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,sourceWord,source1,Nat.unpair_pair] using read
  refine ⟨original,Word.toBitVec_toNat bounded,?_⟩
  exact Word.eq_of_value bounded (Word.ofBitVec_bound _) (by
    rw [Word.ofBitVec_value,Word.toBitVec_toNat bounded])

/-- Actual runtime request fields and original constructor/query identities
    identify the request kind and ABI-high with the same original rs1 read. -/
theorem request_from_source {w : Nat → ZMod mersenne31Modulus} {entry : CSRProgramEntry}
    {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (fields : csrDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (transfer : CSRRegisterTransfer (.mk .reduced w) entry before after)
    (bounded : (sourceWord w).Bounded) : CSRSourceRequest (.mk .reduced w) entry before := by
  have source := source_word transfer bounded
  have decoded := NativeCSRDecoderProofs.decoded_fields fields query
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) decoded.immediate
  change w 9 = (entry.data.immediate.lo : ZMod mersenne31Modulus) at low
  have key : (w 9).val = entry.data.immediate.lo := by
    rw [low,ZMod.val_natCast_of_lt (lt_trans (NativeCSRDecoderProofs.field_bounds fields).1 (by decide))]
  have high : (w 36).val = (sourceWord w).toBitVec.toNat/65536 := by
    have same := congrArg Word.hi source.2.2
    simpa [sourceWord,source1,Word.ofBitVec,limbBase,importedConstraintsMemoryPorts,WordColumns.evaluate] using same
  have highField : w 36 = (((sourceWord w).toBitVec.toNat/65536 : Nat) : ZMod mersenne31Modulus) := by
    rw [← high]
    simp
  refine ⟨(sourceWord w).toBitVec,source.1,source.2.1,source.2.2,?_⟩
  rw [NativeRuntimeCSRResultProofs.request holds decoded.mask,key,low,highField]
  rfl

end Airbender.ReducedMachine.NativeCSRSourceProofs
