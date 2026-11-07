import Airbender.Import.Compiler.LogicalRows.WordMemoryCached
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.WordMemoryCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : Airbender.Compiler.PooledRowNative.WordMemoryCached.Input) :
    Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)) =
      ProgramSetup.packTagged 9 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .wordMemory) (Airbender.Compiler.PooledRowNative.WordMemoryCached.inputRow input).decoderQuery) := by
  rw [← Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[8], 46]
  have left : (Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.payloadExpressions.map (fun expression => expression.eval
      (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])))) := by simp [project, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression9, _root_.Expression.eval]
  have right : ProgramSetup.packTagged 9 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .wordMemory) (Airbender.Compiler.PooledRowNative.WordMemoryCached.inputRow input).decoderQuery) = project (Trace.nativeDecoderQuery
      Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns
      (fun index => (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    Airbender.WordMemory.importedConstraintsTraceColumns Airbender.WordMemory.importedConstraintsDecoderColumns
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : Airbender.Compiler.PooledRowNative.WordMemoryCached.Input) :
    Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : (Airbender.Compiler.DecoderArgumentsNative.WordMemoryCached.native.expression0).eval
      (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : Airbender.Compiler.PooledRowNative.WordMemoryCached.Input) :
    Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ∈ Airbender.Compiler.PooledRowNative.WordMemoryCached.physicalRequests input 0 := by
  have member : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10 ∈ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries :=
    List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries ⟨1, by decide⟩
  exact List.mem_map.mpr ⟨Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.query10, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.WordMemoryCached
