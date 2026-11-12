module
public import Proven.GKRProtocol.DecoderArgumentsNative.UnifiedCached
public import Proven.Compiler.NativeBindings.Unified
public import Proven.Compiler.ScopeTransport
public import Proven.Compiler.SetupMetadata
public import Proven.Compiler.Lookups.Ranges.Unified

@[expose] public section
namespace Airbender.Compiler.NativeDecoder.Unified
open Airbender Trace NativeArithmetic NativePublicSetup
set_option warningAsError true
set_option maxRecDepth 65536

theorem scope : (decoderExpressions Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns).toList.all (NativeBridge.expressionScope 137) = true := by kernel_rfl

/-- The enabled native decoder tuple is the exact public logical projection. -/
theorem tuple (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor .unified) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor .unified) physical assignment) :
    Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)) =
      payload .unified (Trace.nativeDecoderQuery Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns assignment) := by
  have arithmetic := NativeBindings.Unified.scalar_gates physical accepted
  rw [← Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.payload_fields physical (Verification.environment assignment).data arithmetic]
  have left : (Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.payloadExpressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (Verification.environment assignment).data))) =
      payload .unified ((decoderExpressions Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (Verification.environment assignment).data))) := by
    unfold payload maskRow
    rw [NativePublicSetup.Metadata.columns_binding]
    simp [Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression10,
      NativePublicSetup.Metadata.columns, NativePublicSetup.Metadata.hasFunct3, tagged,
      decoderExpressions, decoderFlagExpression, decoderFlagFold]
    rfl
  have same : (decoderExpressions Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (Verification.environment assignment).data)) =
      (decoderExpressions Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Verification.environment assignment)) := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_map]
    apply NativeBridge.expression_transport _ (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (Verification.environment assignment).data) (Verification.environment assignment) 137
    · apply List.all_eq_true.mp scope
      exact List.getElem_mem (by simpa using bound)
    · exact NativeBindings.Unified.environment physical assignment agreement
  exact left.trans ((congrArg (payload .unified) same).trans
    (congrArg (payload .unified) (decoder_expressions_value Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns (Verification.environment assignment))))

/-- Participation selects the captured execute expression through checked placements. -/
theorem enabled (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor .unified) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor .unified) physical assignment)
    (active : assignment Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1) :
    Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.execute_weight physical (Verification.environment assignment).data (NativeBindings.Unified.scalar_gates physical accepted)]
  have same := NativeBindings.Unified.environment physical assignment agreement Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute (by decide +kernel)
  change (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (Verification.environment assignment).data).get Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute ≠ 0
  rw [same]
  exact active ▸ one_ne_zero

/-- Exact natural matching supplies a complete independent public setup row. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor .unified) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor .unified) physical assignment)
    (active : assignment Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute = 1)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (rows initial program .unified)) :
    NativePublicSetup.Proofs.Contains initial program .unified 0
      (payload .unified (Trace.nativeDecoderQuery Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns assignment)) := by
  rw [← tuple physical assignment accepted agreement]
  apply NativeSourceTransport.Unified.source_member (NativeBindings.Unified.scalar_gates physical accepted) arguments 0
    (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)) ?_ (enabled physical assignment accepted agreement active)
  apply List.mem_map.mpr
  refine ⟨Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20, ?_, rfl⟩
  exact List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨5, by decide⟩

end Airbender.Compiler.NativeDecoder.Unified
