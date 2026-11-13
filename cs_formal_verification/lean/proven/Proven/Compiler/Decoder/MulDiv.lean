module
public import Proven.GKRProtocol.DecoderArgumentsNative.MulDivCached
public import Proven.Compiler.NativeBindings.MulDiv
public import Proven.Compiler.ScopeTransport
public import Proven.Compiler.SetupMetadata
public import Proven.Compiler.Lookups.Ranges.MulDiv

@[expose] public section
namespace Airbender.Compiler.NativeDecoder.MulDiv
open Airbender Trace NativeArithmetic NativePublicSetup
set_option warningAsError true
set_option maxRecDepth 65536

theorem scope : (decoderExpressions Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns).toList.all (NativeBridge.expressionScope 71) = true := by kernel_rfl

/-- The enabled native decoder tuple is the exact public logical projection. -/
theorem tuple (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .mulDiv)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .mulDiv)) physical assignment) :
    Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)) =
      payload (.pooled .mulDiv) (Trace.nativeDecoderQuery Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns assignment) := by
  have arithmetic := NativeBindings.MulDiv.scalar_gates physical accepted
  rw [← Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.payload_fields physical (Verification.environment assignment).data arithmetic]
  have left : (Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.payloadExpressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical (Verification.environment assignment).data))) =
      payload (.pooled .mulDiv) ((decoderExpressions Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical (Verification.environment assignment).data))) := by
    unfold payload maskRow
    rw [NativePublicSetup.Metadata.columns_binding]
    simp [Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.expression9,
      NativePublicSetup.Metadata.columns, NativePublicSetup.Metadata.hasFunct3, tagged,
      decoderExpressions, decoderFlagExpression, decoderFlagFold]
    rfl
  have same : (decoderExpressions Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical (Verification.environment assignment).data)) =
      (decoderExpressions Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Verification.environment assignment)) := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_map]
    apply NativeBridge.expression_transport _ (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical (Verification.environment assignment).data) (Verification.environment assignment) 71
    · apply List.all_eq_true.mp scope
      exact List.getElem_mem (by simpa using bound)
    · exact NativeBindings.MulDiv.environment physical assignment agreement
  exact left.trans ((congrArg (payload (.pooled .mulDiv)) same).trans
    (congrArg (payload (.pooled .mulDiv)) (decoder_expressions_value Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns (Verification.environment assignment))))

/-- Participation selects the captured execute expression through checked placements. -/
theorem enabled (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .mulDiv)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .mulDiv)) physical assignment)
    (active : assignment Airbender.MulDiv.importedConstraintsTraceColumns.execute = 1) :
    Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.MulDivCached.native.execute_weight physical (Verification.environment assignment).data (NativeBindings.MulDiv.scalar_gates physical accepted)]
  have same := NativeBindings.MulDiv.environment physical assignment agreement Airbender.MulDiv.importedConstraintsTraceColumns.execute (by decide +kernel)
  change (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical (Verification.environment assignment).data).get Airbender.MulDiv.importedConstraintsTraceColumns.execute ≠ 0
  rw [same]
  exact active ▸ one_ne_zero

/-- Exact natural matching supplies a complete independent public setup row. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .mulDiv)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .mulDiv)) physical assignment)
    (active : assignment Airbender.MulDiv.importedConstraintsTraceColumns.execute = 1)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (rows initial program (.pooled .mulDiv))) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .mulDiv) 0
      (payload (.pooled .mulDiv) (Trace.nativeDecoderQuery Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns assignment)) := by
  rw [← tuple physical assignment accepted agreement]
  apply NativeSourceTransport.MulDiv.source_member (NativeBindings.MulDiv.scalar_gates physical accepted) arguments 0
    (Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)) ?_ (enabled physical assignment accepted agreement active)
  apply List.mem_map.mpr
  refine ⟨Airbender.Compiler.LookupSourceNative.MulDivCached.native.query16, ?_, rfl⟩
  exact List.get_mem Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ⟨8, by decide⟩

end Airbender.Compiler.NativeDecoder.MulDiv
