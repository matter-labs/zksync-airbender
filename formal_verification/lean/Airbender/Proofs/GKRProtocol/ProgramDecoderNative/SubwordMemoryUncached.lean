import Airbender.Import.Compiler.LogicalRows.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.SubwordMemoryUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.Input) :
    Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)) =
      ProgramSetup.packTagged 9 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .subwordMemory) (Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.inputRow input).decoderQuery) := by
  rw [← Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[8], 46]
  have left : (Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.payloadExpressions.map (fun expression => expression.eval
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])))) := by simp [project, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression9, _root_.Expression.eval]
  have right : ProgramSetup.packTagged 9 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .subwordMemory) (Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.inputRow input).decoderQuery) = project (Trace.nativeDecoderQuery
      Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns
      (fun index => (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    Airbender.SubwordMemory.importedConstraintsTraceColumns Airbender.SubwordMemory.importedConstraintsDecoderColumns
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.Input) :
    Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : (Airbender.Compiler.DecoderArgumentsNative.SubwordMemoryUncached.native.expression0).eval
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.Input) :
    Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ∈ Airbender.Compiler.PooledRowNative.SubwordMemoryUncached.physicalRequests input 0 := by
  have member : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12 ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries :=
    List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries ⟨2, by decide⟩
  exact List.mem_map.mpr ⟨Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.SubwordMemoryUncached
