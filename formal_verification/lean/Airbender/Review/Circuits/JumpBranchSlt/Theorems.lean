import Airbender.Review.Circuits.JumpBranchSlt.Model
import Airbender.Proofs.JumpBranchSlt.NativeSetup

namespace Airbender.JumpBranchSlt

/-- Every native row constraint and fixed query derives exact control/cleanup
    observables. This claim does not assert original Sail instruction execution. -/
theorem native_fixed_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    FixedEffects w :=
  Proofs.fixed_effects holds

/-- Supported native opcode masks derive both outgoing PC limb bounds from
    native equations/lookups. Binding the mask to public decoding is separate. -/
theorem native_pc_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mask : (w 12).val ∈ [1, 2, 4, 8, 16]) :
    (w 13).val < 65536 ∧ (w 14).val < 65536 :=
  Proofs.pc_bounds holds mask

/-- Original public bytes and full padded native query membership derive source
    decoding and outgoing PC bounds. Initialized instruction execution is separate. -/
theorem native_public_decoding {w : Nat → ZMod mersenne31Modulus}
    {setup : Trace.SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    Fetched w before ∧ (w 13).val < 65536 ∧ (w 14).val < 65536 :=
  Proofs.public_decoder image holds member

/-- Pinned actual native export membership recovers original public source and
    PC bounds. General Rust decoder and initialized execution remain separate. -/
theorem exported_decoder_soundness {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : ∃ i : Fin 1048576, decoderQuery w = NativeSetup.controlDecoder.row i) :
    Fetched w NativeSetup.before ∧ (w 13).val < 65536 ∧ (w 14).val < 65536 :=
  Proofs.native_exported_source holds member

end Airbender.JumpBranchSlt
