import Airbender.Import.Compiler.LogicalRows.JumpBranchCached
import Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.JumpBranchCached
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths

namespace Airbender.Compiler.ProgramDecoderNative.JumpBranchCached
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem decoder_tuple (input : Airbender.Compiler.PooledRowNative.JumpBranchCached.Input) :
    Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)) =
      ProgramSetup.packTagged 10 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .jumpBranchSlt) (Airbender.Compiler.PooledRowNative.JumpBranchCached.inputRow input).decoderQuery) := by
  rw [← Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.payload_fields input.physical (fun _ _ => #[]) input.arithmetic]
  let project : Vector Source.BaseField 9 → List Source.BaseField := fun row => [row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8], 46]
  have left : (Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.payloadExpressions.map (fun expression => expression.eval
      (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])))) =
      project ((decoderExpressions Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns).map
        (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])))) := by simp [project, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.payloadExpressions, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression1, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression2, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression3, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression4, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression5, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression6, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression7, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression8, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression9, Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression10, _root_.Expression.eval]
  have right : ProgramSetup.packTagged 10 46 (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily .jumpBranchSlt) (Airbender.Compiler.PooledRowNative.JumpBranchCached.inputRow input).decoderQuery) = project (Trace.nativeDecoderQuery
      Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns
      (fun index => (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])).get index)) := by rfl
  exact left.trans ((congrArg project (decoder_expressions_value
    Airbender.JumpBranchSlt.importedConstraintsTraceColumns Airbender.JumpBranchSlt.importedConstraintsDecoderColumns
    (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])))).trans right.symm)

theorem decoder_enabled (input : Airbender.Compiler.PooledRowNative.JumpBranchCached.Input) :
    Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
  rw [Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.execute_weight input.physical (fun _ _ => #[]) input.arithmetic]
  have active : (Airbender.Compiler.DecoderArgumentsNative.JumpBranchCached.native.expression0).eval
      (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])) = 1 := input.active
  rw [active]
  exact one_ne_zero

theorem decoder_member (input : Airbender.Compiler.PooledRowNative.JumpBranchCached.Input) :
    Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ∈ Airbender.Compiler.PooledRowNative.JumpBranchCached.physicalRequests input 0 := by
  have member : Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12 ∈ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries :=
    List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨4, by decide⟩
  exact List.mem_map.mpr ⟨Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.query12, member, rfl⟩

end Airbender.Compiler.ProgramDecoderNative.JumpBranchCached
