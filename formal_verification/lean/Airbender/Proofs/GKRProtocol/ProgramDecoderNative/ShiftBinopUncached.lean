import Airbender.Import.Compiler.LogicalRows.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.ShiftBinopUncached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.Input) :
    Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.query10.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement)) =
      ProgramSetup.packTagged 10 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .shiftBinop) (Airbender.Compiler.PooledRowNative.ShiftBinopUncached.inputRow input).decoderQuery) := by
  rw [← Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8], 46]
  have left : (Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.payloadExpressions.map (fun expression => expression.eval
      (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment input.physical (fun _ _ => #[])))) := by simp [project, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression10, _root_.Expression.eval]
  have right : ProgramSetup.packTagged 10 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .shiftBinop) (Airbender.Compiler.PooledRowNative.ShiftBinopUncached.inputRow input).decoderQuery) = project (Trace.nativeDecoderQuery
      Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns
      (fun index => (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    Airbender.ShiftBinop.importedConstraintsTraceColumns Airbender.ShiftBinop.importedConstraintsDecoderColumns
    (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.Input) :
    Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.query10.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : (Airbender.Compiler.DecoderArgumentsNative.ShiftBinopUncached.native.expression0).eval
      (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : Airbender.Compiler.PooledRowNative.ShiftBinopUncached.Input) :
    Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.query10.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ∈ Airbender.Compiler.PooledRowNative.ShiftBinopUncached.physicalRequests input 0 := by
  have member : Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.query10 ∈ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries :=
    List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries ⟨5, by decide⟩
  exact List.mem_map.mpr ⟨Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.query10, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.ShiftBinopUncached
