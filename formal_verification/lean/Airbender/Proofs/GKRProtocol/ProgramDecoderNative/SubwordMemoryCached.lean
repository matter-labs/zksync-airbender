import Airbender.Import.Compiler.LogicalRows.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.SubwordMemoryCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : Airbender.Compiler.PooledRowNative.SubwordMemoryCached.Input) :
    Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)) =
      ProgramSetup.packTagged 9 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .subwordMemory) (Airbender.Compiler.PooledRowNative.SubwordMemoryCached.inputRow input).decoderQuery) := by
  rw [← Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[8], 46]
  have left : (Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.payloadExpressions.map (fun expression => expression.eval
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical (fun _ _ => #[])))) := by simp [project, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression9, _root_.Expression.eval]
  have right : ProgramSetup.packTagged 9 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .subwordMemory) (Airbender.Compiler.PooledRowNative.SubwordMemoryCached.inputRow input).decoderQuery) = project (Trace.nativeDecoderQuery
      Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns
      (fun index => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : Airbender.Compiler.PooledRowNative.SubwordMemoryCached.Input) :
    Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : (Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryCached.native.expression0).eval
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : Airbender.Compiler.PooledRowNative.SubwordMemoryCached.Input) :
    Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ∈ Airbender.Compiler.PooledRowNative.SubwordMemoryCached.physicalRequests input 0 := by
  have member : Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12 ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries :=
    List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries ⟨2, by decide⟩
  exact List.mem_map.mpr ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.query12, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.SubwordMemoryCached
