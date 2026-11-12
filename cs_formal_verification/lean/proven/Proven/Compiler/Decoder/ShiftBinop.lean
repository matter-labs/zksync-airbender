module
public import Proven.GKRProtocol.DecoderArgumentsNative.ShiftBinopCached
public import Proven.Compiler.NativeBindings.ShiftBinop
public import Proven.Compiler.ScopeTransport
public import Proven.Compiler.SetupMetadata
public import Proven.Compiler.Lookups.Ranges.ShiftBinop

@[expose] public section
namespace Airbender.Compiler.NativeDecoder.ShiftBinop
open Airbender Trace NativeArithmetic NativePublicSetup
set_option warningAsError true
set_option maxRecDepth 65536

theorem scope : (decoderExpressions Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns).toList.all (NativeBridge.expressionScope 98) = true := by kernel_rfl

/-- The enabled native decoder tuple is the exact public logical projection. -/
theorem tuple (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .shiftBinop)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .shiftBinop)) physical assignment) :
    Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)) =
      payload (.pooled .shiftBinop) (Trace.nativeDecoderQuery Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns assignment) := by
  have arithmetic := NativeBindings.ShiftBinop.scalar_gates physical accepted
  rw [← Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.payload_fields physical (Verification.environment assignment).data arithmetic]
  have left : (Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.payloadExpressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (Verification.environment assignment).data))) =
      payload (.pooled .shiftBinop) ((decoderExpressions Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (Verification.environment assignment).data))) := by
    unfold payload maskRow
    rw [NativePublicSetup.Metadata.columns_binding]
    simp [Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.expression10,
      NativePublicSetup.Metadata.columns, NativePublicSetup.Metadata.hasFunct3, tagged,
      decoderExpressions, decoderFlagExpression, decoderFlagFold]
    rfl
  have same : (decoderExpressions Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (Verification.environment assignment).data)) =
      (decoderExpressions Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Verification.environment assignment)) := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_map]
    apply NativeBridge.expression_transport _ (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (Verification.environment assignment).data) (Verification.environment assignment) 98
    · apply List.all_eq_true.mp scope
      exact List.getElem_mem (by simpa using bound)
    · exact NativeBindings.ShiftBinop.environment physical assignment agreement
  exact left.trans ((congrArg (payload (.pooled .shiftBinop)) same).trans
    (congrArg (payload (.pooled .shiftBinop)) (decoder_expressions_value Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns (Verification.environment assignment))))

/-- Participation selects the captured execute expression through checked placements. -/
theorem enabled (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .shiftBinop)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .shiftBinop)) physical assignment)
    (active : assignment Airbender.ShiftBinop.importedConstraintsTraceColumns.execute = 1) :
    Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.ShiftBinopCached.native.execute_weight physical (Verification.environment assignment).data (NativeBindings.ShiftBinop.scalar_gates physical accepted)]
  have same := NativeBindings.ShiftBinop.environment physical assignment agreement Airbender.ShiftBinop.importedConstraintsTraceColumns.execute (by decide +kernel)
  change (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (Verification.environment assignment).data).get Airbender.ShiftBinop.importedConstraintsTraceColumns.execute ≠ 0
  rw [same]
  exact active ▸ one_ne_zero

/-- Exact natural matching supplies a complete independent public setup row. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .shiftBinop)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .shiftBinop)) physical assignment)
    (active : assignment Airbender.ShiftBinop.importedConstraintsTraceColumns.execute = 1)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .shiftBinop))
      (NativeLookups.selectorsFor (.pooled .shiftBinop)) physical (rows initial program (.pooled .shiftBinop))) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .shiftBinop) 0
      (payload (.pooled .shiftBinop) (Trace.nativeDecoderQuery Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns assignment)) := by
  rw [← tuple physical assignment accepted agreement]
  apply NativeSourceTransport.ShiftBinop.source_member (NativeBindings.ShiftBinop.scalar_gates physical accepted) arguments 0
    (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)) ?_ (enabled physical assignment accepted agreement active)
  apply List.mem_map.mpr
  refine ⟨Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.query10, ?_, rfl⟩
  exact List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries ⟨5, by decide⟩

end Airbender.Compiler.NativeDecoder.ShiftBinop
