import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.ShiftBinopUncached

namespace Airbender.Compiler.ProgramPCLowNative.ShiftBinopUncached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.ShiftBinopUncached
set_option warningAsError true
set_option Elab.async false

private theorem final_range_lookup
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.ShiftBinopUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.ShiftBinopUncached.native.range16_clean_refinement _ valid _

/-- Exact native range matching bounds the outgoing PC before decoder use. -/
theorem final_pc_low
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopUncached group index.val) input) : (inputRow input).finish.word.lo < 65536 := by
  change ((Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment input.physical
    (fun _ _ => #[])).get Airbender.ShiftBinop.importedConstraintsTraceColumns.finalPC[0]).val < 65536
  simpa [Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression0, _root_.Expression.eval,
    Airbender.ShiftBinop.importedConstraintsTraceColumns, Arithmetic.limbBase] using
    Verification.range16_bound (final_range_lookup decoder wordAt input arguments (fun _ _ => #[]))

end Airbender.Compiler.ProgramPCLowNative.ShiftBinopUncached
