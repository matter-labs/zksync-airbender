module
public import Proven.GKRProtocol.DecoderArgumentsNative.WordMemoryCached
public import Proven.Compiler.NativeBindings.WordMemory
public import Proven.Compiler.ScopeTransport
public import Proven.Compiler.SetupMetadata
public import Proven.Compiler.Lookups.Ranges.WordMemory

@[expose] public section
namespace Airbender.Compiler.NativeDecoder.WordMemory
open Airbender Trace NativeArithmetic NativePublicSetup
set_option warningAsError true
set_option maxRecDepth 65536

theorem scope : (decoderExpressions Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns).toList.all (NativeBridge.expressionScope 52) = true := by kernel_rfl

/-- The enabled native decoder tuple is the exact public logical projection. -/
theorem tuple (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .wordMemory)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .wordMemory)) physical assignment) :
    Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)) =
      payload (.pooled .wordMemory) (Trace.nativeDecoderQuery Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns assignment) := by
  have arithmetic := NativeBindings.WordMemory.scalar_gates physical accepted
  rw [← Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.payload_fields physical (Verification.environment assignment).data arithmetic]
  have left : (Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.payloadExpressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment assignment).data))) =
      payload (.pooled .wordMemory) ((decoderExpressions Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment assignment).data))) := by
    unfold payload maskRow
    rw [NativePublicSetup.Metadata.columns_binding]
    simp [Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression9,
      NativePublicSetup.Metadata.columns, NativePublicSetup.Metadata.hasFunct3, tagged,
      decoderExpressions, decoderFlagExpression, decoderFlagFold]
    rfl
  have same : (decoderExpressions Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment assignment).data)) =
      (decoderExpressions Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Verification.environment assignment)) := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_map]
    apply NativeBridge.expression_transport _ (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment assignment).data) (Verification.environment assignment) 52
    · apply List.all_eq_true.mp scope
      exact List.getElem_mem (by simpa using bound)
    · exact NativeBindings.WordMemory.environment physical assignment agreement
  exact left.trans ((congrArg (payload (.pooled .wordMemory)) same).trans
    (congrArg (payload (.pooled .wordMemory)) (decoder_expressions_value Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns (Verification.environment assignment))))

/-- Participation selects the captured execute expression through checked placements. -/
theorem enabled (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .wordMemory)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .wordMemory)) physical assignment)
    (active : assignment Airbender.WordMemory.importedConstraintsTraceColumns.execute = 1) :
    Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.execute_weight physical (Verification.environment assignment).data (NativeBindings.WordMemory.scalar_gates physical accepted)]
  have same := NativeBindings.WordMemory.environment physical assignment agreement Airbender.WordMemory.importedConstraintsTraceColumns.execute (by decide +kernel)
  change (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment assignment).data).get Airbender.WordMemory.importedConstraintsTraceColumns.execute ≠ 0
  rw [same]
  exact active ▸ one_ne_zero

/-- Exact natural matching supplies a complete independent public setup row. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .wordMemory)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .wordMemory)) physical assignment)
    (active : assignment Airbender.WordMemory.importedConstraintsTraceColumns.execute = 1)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .wordMemory))
      (NativeLookups.selectorsFor (.pooled .wordMemory)) physical (rows initial program (.pooled .wordMemory))) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .wordMemory) 0
      (payload (.pooled .wordMemory) (Trace.nativeDecoderQuery Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns assignment)) := by
  rw [← tuple physical assignment accepted agreement]
  apply NativeSourceTransport.WordMemory.source_member (NativeBindings.WordMemory.scalar_gates physical accepted) arguments 0
    (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)) ?_ (enabled physical assignment accepted agreement active)
  apply List.mem_map.mpr
  refine ⟨Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10, ?_, rfl⟩
  exact List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries ⟨1, by decide⟩

end Airbender.Compiler.NativeDecoder.WordMemory
