import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.ShiftBinopCached

namespace Airbender.Compiler.ProgramPCLowNative.ShiftBinopCached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.ShiftBinopCached
set_option warningAsError true
set_option Elab.async false

private theorem final_range_lookup
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.ShiftBinopCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.ShiftBinopCached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.ShiftBinopCached.native.range16_clean_refinement _ valid _

/-- Exact native range matching bounds the outgoing PC before decoder use. -/
theorem final_pc_low
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopCached group index.val) input) : (inputRow input).finish.word.lo < 65536 := by
  change ((Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical
    (fun _ _ => #[])).get Airbender.ShiftBinop.importedConstraintsTraceColumns.finalPC[0]).val < 65536
  simpa [Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.rangeExpression0, _root_.Expression.eval,
    Airbender.ShiftBinop.importedConstraintsTraceColumns, Arithmetic.limbBase] using
    Verification.range16_bound (final_range_lookup decoder wordAt input arguments (fun _ _ => #[]))

end Airbender.Compiler.ProgramPCLowNative.ShiftBinopCached
