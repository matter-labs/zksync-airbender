import Airbender.Review.Trace.Families.ReducedMachine.CSRRequests

namespace Tests.NativeReducedCSRRequests
open Airbender Arithmetic Trace ReducedMachine Native Verification
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Nondeterminism never creates a delegation request, for any source word. -/
theorem nondeterminism_reference (source : BitVec 32) :
    csrRequestReference 1984 source = ⟨0,0,some 0,3⟩ := by
  simp [csrRequestReference,NativeRuntimeCSR.delegated]

/-- The observed ABI index is the natural high half, before casting to M31. -/
theorem delegation_reference (source : BitVec 32) :
    csrRequestReference 1991 source =
      ⟨1,1991,some (((source.toNat/65536 : Nat) : ZMod mersenne31Modulus)),3⟩ := by
  simp [csrRequestReference,NativeRuntimeCSR.delegated]

theorem abi_below_boundary : csrRequestReference 1991 (0x0000ffff : BitVec 32) =
    ⟨1,1991,some 0,3⟩ := by decide

theorem abi_at_boundary : csrRequestReference 1991 (0x00010000 : BitVec 32) =
    ⟨1,1991,some 1,3⟩ := by decide

theorem abi_independent_low_half : csrRequestReference 1991 (0x12345678 : BitVec 32) =
    csrRequestReference 1991 (0x1234ffff : BitVec 32) := by decide

/-- Full RV32 sources above the field modulus retain their architectural high half. -/
theorem abi_full_rv32_max : csrRequestReference 1991 (0xffffffff : BitVec 32) =
    ⟨1,1991,some 65535,3⟩ := by decide

/-- The original GPR read, not a reduced field representative, determines the ABI. -/
theorem abi_above_field : csrRequestReference 1991 (0x80000000 : BitVec 32) =
    ⟨1,1991,some 32768,3⟩ := by decide

/-- Conditional native check: an actual accepted local row and its real GPR
    history cannot report a request different from that same pre-state source. -/
theorem wrong_original_source_request_rejected
    {w : Nat → ZMod mersenne31Modulus} {entry : CSRProgramEntry}
    {cells : List Cell} {before after : State} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (fields : csrDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeCSRPortProofs.nativeEvents epoch w).reverse before after)
    (bounded : (sourceWord w).Bounded)
    (bad : csrRequest w ≠ csrRequestReference entry.data.immediate.lo (sourceWord w).toBitVec) : False := by
  have transfer : CSRRegisterTransfer (.mk .reduced w) entry before after :=
    ⟨NativeCSRPortProofs.register_reads epoch native fields query history,
      NativeCSRPortProofs.register_write epoch native fields query history⟩
  obtain ⟨value,read,canonical,limbs,request⟩ :=
    NativeCSRSourceProofs.request_from_source native fields query transfer bounded
  have equal : value = (sourceWord w).toBitVec := by
    rw [limbs,Word.ofBitVec_roundtrip]
  exact bad (by simpa [equal] using request)

end Tests.NativeReducedCSRRequests
