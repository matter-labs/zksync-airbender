import Airbender.Import.Compiler.LogicalRows.AddSubUncached
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.AddSubUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : Airbender.Compiler.PooledRowNative.AddSubUncached.Input) :
    Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)) =
      ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .addSub) (Airbender.Compiler.PooledRowNative.AddSubUncached.inputRow input).decoderQuery := by
  rw [← Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[8]]
  have left : (Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.payloadExpressions.map (fun expression => expression.eval
      (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])))) := by simp [project, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression8]
  have right : ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .addSub) (Airbender.Compiler.PooledRowNative.AddSubUncached.inputRow input).decoderQuery = project (Trace.nativeDecoderQuery
      Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns
      (fun index => (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    Airbender.AddSub.importedConstraintsTraceColumns Airbender.AddSub.importedConstraintsDecoderColumns
    (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : Airbender.Compiler.PooledRowNative.AddSubUncached.Input) :
    Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : (Airbender.Compiler.DecoderArgumentsNative.AddSubUncached.native.expression0).eval
      (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : Airbender.Compiler.PooledRowNative.AddSubUncached.Input) :
    Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) ∈ Airbender.Compiler.PooledRowNative.AddSubUncached.physicalRequests input 0 := by
  have member : Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14 ∈ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.genericQueries :=
    List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.genericQueries ⟨0, by decide⟩
  exact List.mem_map.mpr ⟨Airbender.Compiler.LookupSourceNative.AddSubUncached.native.query14, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.AddSubUncached
