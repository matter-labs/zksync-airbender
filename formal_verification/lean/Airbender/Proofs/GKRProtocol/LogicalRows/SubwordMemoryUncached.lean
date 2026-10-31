import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.SubwordMemoryUncached
import Airbender.Import.Compiler.LogicalRows.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.PooledRowNative.SubwordMemoryUncached

namespace Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem input_constraints (input : Input) (arguments : LookupArguments input) {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (_physical : Trace.initialImage before cells = some tokens)
    (_domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨Trace.ROM.table cells tokens,
        Verification.subwordTable (Trace.ROM.words before)⟩ : Trace.PooledSetup babyBearModulus)) := by
  have native := Airbender.Compiler.PhysicalClosedNative.SubwordMemoryUncached.retained_clock_from_physical
    input.physical (fun _ _ => #[]) input.arithmetic (helpers_from_arguments input arguments)
    (authored_from_arguments input arguments)
  exact PublicConstraints.subword_transport _ _ _ native
    (fun _ member guard => ROMNative.SubwordPublic.public_table_refinement image member guard)

/-- Decode by transporting physical table membership directly through the
checked decoder-payload geometry. No canonical borrow frame is needed. -/
theorem input_decoded (input : Input) (arguments : LookupArguments input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.pooledProgram (inputRow input).family).Contains #[]
      (inputRow input).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.SubwordMemoryUncached.program_from_source_membership (by decide +kernel)
    input.physical (fun _ _ => #[]) input.arithmetic typed
  apply (authored_from_arguments input arguments).1 Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12
    Airbender.Compiler.DecoderQueryNative.SubwordMemoryUncached.decoder_query_member
  rw [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have enabled : (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1 := input.active
  have nonzero : (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])).get
      Airbender.SubwordMemory.importedConstraintsTraceColumns.execute ≠ 0 :=
    fun zero => one_ne_zero (enabled.symm.trans zero)
  simpa [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression0, _root_.Expression.eval] using nonzero

end Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
