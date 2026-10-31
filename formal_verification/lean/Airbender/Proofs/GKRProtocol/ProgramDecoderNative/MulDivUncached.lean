import Airbender.Import.Compiler.LogicalRows.MulDivUncached
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.MulDivUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : Airbender.Compiler.PooledRowNative.MulDivUncached.Input) :
    Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)) =
      ProgramSetup.packTagged 9 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .mulDiv) (Airbender.Compiler.PooledRowNative.MulDivUncached.inputRow input).decoderQuery) := by
  rw [← Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[8], 46]
  have left : (Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.payloadExpressions.map (fun expression => expression.eval
      (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])))) := by simp [project, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression9, _root_.Expression.eval]
  have right : ProgramSetup.packTagged 9 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .mulDiv) (Airbender.Compiler.PooledRowNative.MulDivUncached.inputRow input).decoderQuery) = project (Trace.nativeDecoderQuery
      Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns
      (fun index => (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    Airbender.MulDiv.importedConstraintsTraceColumns Airbender.MulDiv.importedConstraintsDecoderColumns
    (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : Airbender.Compiler.PooledRowNative.MulDivUncached.Input) :
    Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : (Airbender.Compiler.DecoderArgumentsNative.MulDivUncached.native.expression0).eval
      (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : Airbender.Compiler.PooledRowNative.MulDivUncached.Input) :
    Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ∈ Airbender.Compiler.PooledRowNative.MulDivUncached.physicalRequests input 0 := by
  have member : Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16 ∈ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries :=
    List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨8, by decide⟩
  exact List.mem_map.mpr ⟨Airbender.Compiler.LookupSourceNative.MulDivUncached.native.query16, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.MulDivUncached
