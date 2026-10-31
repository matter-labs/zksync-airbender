import Airbender.Import.Compiler.LogicalRows.UnifiedUncached
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.UnifiedUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.Input) :
    Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.query20.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)) =
      ProgramSetup.packTagged 10 46 (ProgramRows.maskRow ProgramRows.Proofs.unifiedMask (Airbender.Compiler.UnifiedRowNative.UnifiedUncached.inputRow input).decoderQuery) := by
  rw [← Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8], 46]
  have left : (Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.payloadExpressions.map (fun expression => expression.eval
      (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])))) := by simp [project, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression10, _root_.Expression.eval]
  have right : ProgramSetup.packTagged 10 46 (ProgramRows.maskRow ProgramRows.Proofs.unifiedMask (Airbender.Compiler.UnifiedRowNative.UnifiedUncached.inputRow input).decoderQuery) = project (Trace.nativeDecoderQuery
      Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns
      (fun index => (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    Airbender.UnifiedReduced.importedConstraintsTraceColumns Airbender.UnifiedReduced.importedConstraintsDecoderColumns
    (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.Input) :
    Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.query20.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : (Airbender.Compiler.DecoderArgumentsNative.UnifiedUncached.native.expression0).eval
      (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : Airbender.Compiler.UnifiedRowNative.UnifiedUncached.Input) :
    Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.query20.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ∈ Airbender.Compiler.UnifiedRowNative.UnifiedUncached.physicalRequests input 0 := by
  have member : Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.query20 ∈ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries :=
    List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨5, by decide⟩
  exact List.mem_map.mpr ⟨Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.query20, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.UnifiedUncached
