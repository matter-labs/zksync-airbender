module
public import Proven.GKRProtocol.DecoderArgumentsNative.SubwordMemoryCached
public import Proven.Compiler.NativeBindings.SubwordMemory
public import Proven.Compiler.ScopeTransport
public import Proven.Compiler.SetupMetadata
public import Proven.Compiler.Lookups.Ranges.SubwordMemory

@[expose] public section
namespace Airbender.Compiler.NativeDecoder.SubwordMemory
open Airbender Trace NativeArithmetic NativePublicSetup
set_option warningAsError true
set_option maxRecDepth 65536

theorem scope : (decoderExpressions Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns).toList.all (NativeBridge.expressionScope 68) = true := by kernel_rfl

/-- The enabled native decoder tuple is the exact public logical projection. -/
theorem tuple (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .subwordMemory)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .subwordMemory)) physical assignment) :
    Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)) =
      payload (.pooled .subwordMemory) (Trace.nativeDecoderQuery Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns assignment) := by
  have arithmetic := NativeBindings.SubwordMemory.scalar_gates physical accepted
  rw [← Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.payload_fields physical (Verification.environment assignment).data arithmetic]
  have left : (Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.payloadExpressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical (Verification.environment assignment).data))) =
      payload (.pooled .subwordMemory) ((decoderExpressions Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical (Verification.environment assignment).data))) := by
    unfold payload maskRow
    rw [NativePublicSetup.Metadata.columns_binding]
    simp [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression9,
      NativePublicSetup.Metadata.columns, NativePublicSetup.Metadata.hasFunct3, tagged,
      decoderExpressions, decoderFlagExpression, decoderFlagFold]
    rfl
  have same : (decoderExpressions Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical (Verification.environment assignment).data)) =
      (decoderExpressions Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Verification.environment assignment)) := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_map]
    apply NativeBridge.expression_transport _ (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical (Verification.environment assignment).data) (Verification.environment assignment) 68
    · apply List.all_eq_true.mp scope
      exact List.getElem_mem (by simpa using bound)
    · exact NativeBindings.SubwordMemory.environment physical assignment agreement
  exact left.trans ((congrArg (payload (.pooled .subwordMemory)) same).trans
    (congrArg (payload (.pooled .subwordMemory)) (decoder_expressions_value Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns (Verification.environment assignment))))

/-- Participation selects the captured execute expression through checked placements. -/
theorem enabled (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .subwordMemory)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .subwordMemory)) physical assignment)
    (active : assignment Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1) :
    Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.execute_weight physical (Verification.environment assignment).data (NativeBindings.SubwordMemory.scalar_gates physical accepted)]
  have same := NativeBindings.SubwordMemory.environment physical assignment agreement Airbender.SubwordMemory.importedConstraintsTraceColumns.execute (by decide +kernel)
  change (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical (Verification.environment assignment).data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.execute ≠ 0
  rw [same]
  exact active ▸ one_ne_zero

/-- Exact natural matching supplies a complete independent public setup row. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .subwordMemory)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .subwordMemory)) physical assignment)
    (active : assignment Airbender.SubwordMemory.importedConstraintsTraceColumns.execute = 1)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (rows initial program (.pooled .subwordMemory))) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 0
      (payload (.pooled .subwordMemory) (Trace.nativeDecoderQuery Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns assignment)) := by
  rw [← tuple physical assignment accepted agreement]
  apply NativeSourceTransport.SubwordMemory.source_member (NativeBindings.SubwordMemory.scalar_gates physical accepted) arguments 0
    (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)) ?_ (enabled physical assignment accepted agreement active)
  apply List.mem_map.mpr
  refine ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12, ?_, rfl⟩
  exact List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries ⟨2, by decide⟩

end Airbender.Compiler.NativeDecoder.SubwordMemory
