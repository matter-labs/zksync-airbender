import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.UnifiedCached
import Airbender.Import.Compiler.LogicalRows.UnifiedCached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.UnifiedRowNative.UnifiedCached

namespace Airbender.Compiler.UnifiedRowNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem input_native_constraints (input : Input) (arguments : LookupArguments input) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints Airbender.Compiler.CleanClosedNative.UnifiedCached.nativeSetup) :=
  Airbender.Compiler.PhysicalClosedNative.UnifiedCached.retained_clock_from_physical
    input.physical (fun _ _ => #[]) input.arithmetic (helpers_from_arguments input arguments)
    (authored_from_arguments input arguments)

/-- Decode by transporting physical table membership directly through the
checked decoder-payload geometry. No canonical borrow frame is needed. -/
theorem input_decoded (input : Input) (arguments : LookupArguments input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.unifiedProgram (inputRow input).family).Contains #[]
      (inputRow input).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.UnifiedCached.program_from_source_membership (by decide +kernel)
    input.physical (fun _ _ => #[]) input.arithmetic typed
  apply (authored_from_arguments input arguments).1 Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20
    Airbender.Compiler.DecoderQueryNative.UnifiedCached.decoder_query_member
  rw [Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have enabled : (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1 := input.active
  have nonzero : (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute ≠ 0 :=
    fun zero => one_ne_zero (enabled.symm.trans zero)
  simpa [Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression0, _root_.Expression.eval] using nonzero

theorem input_constraints (input : Input) (arguments : LookupArguments input)
    {before : Reference.RiscV.Sail.State} (image : Trace.ROM.ImportedImage before)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (UnifiedReduced.Setup.table before)) := by
  have member := input_decoded input arguments typed
  have operation := UnifiedProgramProfile.query_operation (inputRow input).assignment member
  exact UnifiedPublicConstraints.transport _ _ _ (input_native_constraints input arguments)
    (input_active input) operation
    (fun _ present guard => ROMNative.UnifiedFullPublic.public_table_refinement image present guard)

end Airbender.Compiler.UnifiedRowNative.UnifiedCached
