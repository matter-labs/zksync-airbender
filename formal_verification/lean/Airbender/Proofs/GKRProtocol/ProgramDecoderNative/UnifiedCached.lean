import Airbender.Import.Compiler.LogicalRows.UnifiedCached
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.UnifiedCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : Airbender.Compiler.UnifiedRowNative.UnifiedCached.Input) :
    Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)) =
      ProgramSetup.packTagged 10 46 (ProgramRows.maskRow ProgramRows.Proofs.unifiedMask (Airbender.Compiler.UnifiedRowNative.UnifiedCached.inputRow input).decoderQuery) := by
  rw [← Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8], 46]
  have left : (Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.payloadExpressions.map (fun expression => expression.eval
      (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment input.physical (fun _ _ => #[])))) := by simp [project, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression10, _root_.Expression.eval]
  have right : ProgramSetup.packTagged 10 46 (ProgramRows.maskRow ProgramRows.Proofs.unifiedMask (Airbender.Compiler.UnifiedRowNative.UnifiedCached.inputRow input).decoderQuery) = project (Trace.nativeDecoderQuery
      Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns
      (fun index => (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns
    (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : Airbender.Compiler.UnifiedRowNative.UnifiedCached.Input) :
    Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : (Airbender.Compiler.DecoderArgumentsNative.UnifiedCached.native.expression0).eval
      (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : Airbender.Compiler.UnifiedRowNative.UnifiedCached.Input) :
    Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ∈ Airbender.Compiler.UnifiedRowNative.UnifiedCached.physicalRequests input 0 := by
  have member : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20 ∈ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries :=
    List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨5, by decide⟩
  exact List.mem_map.mpr ⟨Airbender.Compiler.LookupSourceNative.UnifiedCached.native.query20, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.UnifiedCached
