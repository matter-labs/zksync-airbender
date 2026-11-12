module
public import Proven.GKRProtocol.DecoderArgumentsNative.AddSubCached
public import Proven.Compiler.NativeBindings.AddSub
public import Proven.Compiler.ScopeTransport
public import Proven.Compiler.SetupMetadata
public import Proven.Compiler.Lookups.Ranges.AddSub

@[expose] public section
namespace Airbender.Compiler.NativeDecoder.AddSub
open Airbender Trace NativeArithmetic NativePublicSetup
set_option warningAsError true
set_option maxRecDepth 65536

theorem scope : (decoderExpressions Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns).toList.all (NativeBridge.expressionScope 48) = true := by kernel_rfl

/-- The enabled native decoder tuple is the exact public logical projection. -/
theorem tuple (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .addSub)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .addSub)) physical assignment) :
    Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)) =
      payload (.pooled .addSub) (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns assignment) := by
  have arithmetic := NativeBindings.AddSub.scalar_gates physical accepted
  rw [← Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.payload_fields physical (Verification.environment assignment).data arithmetic]
  have left : (Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.payloadExpressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment assignment).data))) =
      payload (.pooled .addSub) ((decoderExpressions Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment assignment).data))) := by
    unfold payload maskRow
    rw [NativePublicSetup.Metadata.columns_binding]
    simp [Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.expression8,
      NativePublicSetup.Metadata.columns, NativePublicSetup.Metadata.hasFunct3, tagged,
      decoderExpressions, decoderFlagExpression, decoderFlagFold]
  have same : (decoderExpressions Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment assignment).data)) =
      (decoderExpressions Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Verification.environment assignment)) := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_map]
    apply NativeBridge.expression_transport _ (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment assignment).data) (Verification.environment assignment) 48
    · apply List.all_eq_true.mp scope
      exact List.getElem_mem (by simpa using bound)
    · exact NativeBindings.AddSub.environment physical assignment agreement
  exact left.trans ((congrArg (payload (.pooled .addSub)) same).trans
    (congrArg (payload (.pooled .addSub)) (decoder_expressions_value Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns (Verification.environment assignment))))

/-- Participation selects the captured execute expression through checked placements. -/
theorem enabled (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .addSub)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .addSub)) physical assignment)
    (active : assignment Airbender.AddSub.importedConstraintsTraceColumns.execute = 1) :
    Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.AddSubCached.native.execute_weight physical (Verification.environment assignment).data (NativeBindings.AddSub.scalar_gates physical accepted)]
  have same := NativeBindings.AddSub.environment physical assignment agreement Airbender.AddSub.importedConstraintsTraceColumns.execute (by decide +kernel)
  change (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment assignment).data).get Airbender.AddSub.importedConstraintsTraceColumns.execute ≠ 0
  rw [same]
  exact active ▸ one_ne_zero

/-- Exact natural matching supplies a complete independent public setup row. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .addSub)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .addSub)) physical assignment)
    (active : assignment Airbender.AddSub.importedConstraintsTraceColumns.execute = 1)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .addSub))
      (NativeLookups.selectorsFor (.pooled .addSub)) physical (rows initial program (.pooled .addSub))) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .addSub) 0
      (payload (.pooled .addSub) (Trace.nativeDecoderQuery Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns assignment)) := by
  rw [← tuple physical assignment accepted agreement]
  apply NativeSourceTransport.AddSub.source_member (NativeBindings.AddSub.scalar_gates physical accepted) arguments 0
    (Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)) ?_ (enabled physical assignment accepted agreement active)
  apply List.mem_map.mpr
  refine ⟨Airbender.Compiler.LookupSourceNative.AddSubCached.native.query14, ?_, rfl⟩
  exact List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries ⟨0, by decide⟩

end Airbender.Compiler.NativeDecoder.AddSub
