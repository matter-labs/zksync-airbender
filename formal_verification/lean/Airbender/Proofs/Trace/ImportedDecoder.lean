import Airbender.Review.Helpers.Decoder.SelectedProgram
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.Soundness
import Airbender.Review.Trace.UnifiedReduced.Theorems
import Airbender.Proofs.Tables.ImportedPooledDecoder
import Airbender.Proofs.Tables.ImportedUnifiedDecoder
import Airbender.Proofs.UnifiedReduced.Tables.ImportedROM
import Airbender.Review.Helpers.UnifiedReduced.ImportedInputs

namespace Airbender.Trace.Proofs

/-- Actual complete selected-program decoder setup supplies pooled decoding.
    The existing public boot, ROM, platform, verifier and logical matching
    boundaries are retained. Incoming PC-low typing follows from constraints
    and state matching; no table-content equivalence is a premise. -/
theorem pooled_imported_decoder_soundness
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : PooledTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell}
    (inputs : PooledBootInputs trace before cells NativeDecoder.pooledProgram)
    (accepted : Accepted trace) (decoded : NativeDecoder.PooledLookups trace) :
    Realizes (PooledStep NativeDecoder.pooledProgram) trace before cells
      (ROMView.token before) := by
  apply _root_.Airbender.Trace.pooled_native_soundness inputs accepted
  apply NativeDecoder.Proofs.pooled_decoded (by decide) accepted ?_ decoded
  rw [inputs.initialBoundary]
  decide +kernel

end Airbender.Trace.Proofs

namespace Airbender.UnifiedReduced.Proofs

/-- Actual selected unified decoder rows, unsupported slots and the committed
    tail replace the modeled decoder-membership premise. Generalized programs
    keep their original claims; this entry explicitly selects the imported text. -/
theorem imported_decoder_execution_soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell}
    (inputs : ImportedExecutionInputs trace initial cells Trace.NativeDecoder.unifiedProgram)
    (accepted : Trace.Accepted trace) (decoded : Trace.NativeDecoder.UnifiedLookups trace) :
    Trace.Realizes (Step Trace.NativeDecoder.unifiedProgram) trace initial cells
      (Trace.ROMView.token initial) := by
  have semantic : ExecutionInputs trace initial cells Trace.NativeDecoder.unifiedProgram := {
    boot := {
      distinct := inputs.boot.distinct
      aligned := inputs.boot.aligned
      profile := inputs.boot.profile
      image := inputs.boot.image
      seed := inputs.boot.seed
      initialPC := inputs.boot.initialPC
      programImage := inputs.boot.programImage
      setup := inputs.boot.setup.trans (Setup.Proofs.imported_table_before inputs.boot.importedImage) }
    registers := inputs.registers
    code := inputs.code
    configuration := inputs.configuration
    ordinary := inputs.ordinary
    landingPadDisabled := inputs.landingPadDisabled
    loads := inputs.loads }
  apply _root_.Airbender.UnifiedReduced.execution_soundness hp clockInverse byteInverse semantic accepted
  apply Trace.NativeDecoder.Proofs.unified_decoded (by omega) accepted ?_ decoded
  rw [inputs.boot.initialPC]
  simp [PCState.boundary, PCState.encode, PCState.State.word, Arithmetic.limbBase]

end Airbender.UnifiedReduced.Proofs
