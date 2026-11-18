module
public import Proven.GKRProtocol.DecoderArgumentsNative.JumpBranchCached
public import Proven.Compiler.NativeBindings.JumpBranch
public import Proven.Compiler.ScopeTransport
public import Proven.Compiler.SetupMetadata
public import Proven.Compiler.Lookups.Ranges.JumpBranch

@[expose] public section
namespace Airbender.Compiler.NativeDecoder.JumpBranch
open Airbender Trace NativeArithmetic NativePublicSetup
set_option warningAsError true
set_option maxRecDepth 65536

theorem scope : (decoderExpressions Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns).toList.all (NativeBridge.expressionScope 55) = true := by kernel_rfl

/-- The enabled native decoder tuple is the exact public logical projection. -/
theorem tuple (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical assignment) :
    Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)) =
      payload (.pooled .jumpBranchSlt) (Trace.nativeDecoderQuery Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns assignment) := by
  have arithmetic := NativeBindings.JumpBranch.scalar_gates physical accepted
  rw [← Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.payload_fields physical (Verification.environment assignment).data arithmetic]
  have left : (Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.payloadExpressions.map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical (Verification.environment assignment).data))) =
      payload (.pooled .jumpBranchSlt) ((decoderExpressions Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical (Verification.environment assignment).data))) := by
    unfold payload maskRow
    rw [NativePublicSetup.Metadata.columns_binding]
    simp [Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression10,
      NativePublicSetup.Metadata.columns, NativePublicSetup.Metadata.hasFunct3, tagged,
      decoderExpressions, decoderFlagExpression, decoderFlagFold]
    rfl
  have same : (decoderExpressions Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical (Verification.environment assignment).data)) =
      (decoderExpressions Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns).map (fun expression => expression.eval (Verification.environment assignment)) := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_map]
    apply NativeBridge.expression_transport _ (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical (Verification.environment assignment).data) (Verification.environment assignment) 55
    · apply List.all_eq_true.mp scope
      exact List.getElem_mem (by simpa using bound)
    · exact NativeBindings.JumpBranch.environment physical assignment agreement
  exact left.trans ((congrArg (payload (.pooled .jumpBranchSlt)) same).trans
    (congrArg (payload (.pooled .jumpBranchSlt)) (decoder_expressions_value Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns (Verification.environment assignment))))

/-- Participation selects the captured execute expression through checked placements. -/
theorem enabled (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical assignment)
    (active : assignment Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute = 1) :
    Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.execute_weight physical (Verification.environment assignment).data (NativeBindings.JumpBranch.scalar_gates physical accepted)]
  have same := NativeBindings.JumpBranch.environment physical assignment agreement Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute (by decide +kernel)
  change (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical (Verification.environment assignment).data).get Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute ≠ 0
  rw [same]
  exact active ▸ one_ne_zero

/-- Exact natural matching supplies a complete independent public setup row. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical assignment)
    (active : assignment Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute = 1)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (rows initial program (.pooled .jumpBranchSlt))) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .jumpBranchSlt) 0
      (payload (.pooled .jumpBranchSlt) (Trace.nativeDecoderQuery Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns assignment)) := by
  rw [← tuple physical assignment accepted agreement]
  apply NativeSourceTransport.JumpBranch.source_member (NativeBindings.JumpBranch.scalar_gates physical accepted) arguments 0
    (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)) ?_ (enabled physical assignment accepted agreement active)
  apply List.mem_map.mpr
  refine ⟨Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12, ?_, rfl⟩
  exact List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨4, by decide⟩

end Airbender.Compiler.NativeDecoder.JumpBranch
