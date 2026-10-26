import Airbender.Import.Compiler.Rows.UnifiedUncached
import Airbender.Proofs.GKRProtocol.WindowedNative.UnifiedUncachedPublic
import Airbender.Proofs.GKRProtocol.CleanClosedNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.DecoderQueryNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.FramedWitnessNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.UnifiedProgramProfile
import Airbender.Proofs.GKRProtocol.UnifiedPublicConstraints

namespace Airbender.Compiler.UnifiedRowNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- A complete native graph witness supplies the arithmetic, canonical frame
and helper range fields of the execution cert without additional claims. -/
def ofWitness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputs.length → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.length → Source.BaseField)
    (index : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length)
    (fallback physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (native : Airbender.Compiler.FramedWitnessNative.UnifiedUncached.CompleteRowWitness hom challenges gamma sourceValue counts index fallback physical values)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedUncached.AuthoredLookupValid sourceValue)
    (active : (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical (fun _ _ => #[])).get
      Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1) : Certificate := by
  rcases native.1 with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩
  exact ⟨sourceValue, counts, physical, inputsAt, arithmetic, helpers, authored, active⟩

/-- The actual independently chosen initialization windows preserve the same
source frame used by execution. Their native products remain in the witness. -/
def ofWindowedWitness (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputs.length → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.length → Source.BaseField)
    (index : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length)
    (fallback physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (native : Airbender.Compiler.WindowedNative.UnifiedUncached.CompleteActualRowWitness publicTops hom challenges gamma sourceValue counts index fallback physical values)
    (authored : Airbender.Compiler.MaterializedWitnessNative.UnifiedUncached.AuthoredLookupValid sourceValue)
    (active : (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment physical (fun _ _ => #[])).get
      Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1) : Certificate := by
  rcases native.1 with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩
  exact ⟨sourceValue, counts, physical, inputsAt, arithmetic, helpers, authored, active⟩


theorem active (cert : Certificate) :
    (row cert).assignment (row cert).columns.execute = 1 := cert.active

theorem native_constraints (cert : Certificate) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row cert).assignment)
      ((row cert).constraints Airbender.Compiler.CleanClosedNative.UnifiedUncached.nativeSetup) := by
  have native := Airbender.Compiler.CleanClosedNative.UnifiedUncached.retained_clock_from_source cert.sourceValue cert.counts
    cert.physical (fun _ _ => #[]) cert.frame cert.arithmetic cert.helpers cert.authored
  exact native

theorem decoded (cert : Certificate)
    (typed : (row cert).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.unifiedProgram (row cert).family).Contains #[]
      (row cert).decoderQuery := by
  apply Airbender.Compiler.DecoderQueryNative.UnifiedUncached.program_from_framed_source (by decide +kernel)
    cert.sourceValue cert.counts cert.physical (fun _ _ => #[])
    cert.frame cert.arithmetic typed ?_ cert.authored
  have enabled := cert.active
  simpa [Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression0, _root_.Expression.eval] using
    (show ((Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment cert.physical (fun _ _ => #[])).get
      Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute) ≠ 0 by rw [enabled]; exact one_ne_zero)


theorem constraints (cert : Certificate) {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before)
    (typed : (row cert).decoderQuery[0].val < 65536) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row cert).assignment)
      ((row cert).constraints (UnifiedReduced.Setup.table before)) := by
  have member := decoded cert typed
  have operation := UnifiedProgramProfile.query_operation (row cert).assignment member
  exact UnifiedPublicConstraints.transport _ _ _ (native_constraints cert) (active cert) operation
    (fun _ present guard => ROMNative.UnifiedFullPublic.public_table_refinement image present guard)

end Airbender.Compiler.UnifiedRowNative.UnifiedUncached
