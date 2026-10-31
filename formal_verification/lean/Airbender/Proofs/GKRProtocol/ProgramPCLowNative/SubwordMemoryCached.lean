import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.SubwordMemoryCached

namespace Airbender.Compiler.ProgramPCLowNative.SubwordMemoryCached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.SubwordMemoryCached
set_option warningAsError true
set_option Elab.async false

private theorem final_range_lookup
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .subwordMemoryCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.get ⟨3, by decide⟩
  have member := ProgramFixedLookup.SubwordMemoryCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryCached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.range_value3 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryCached.native.range16_clean_refinement _ valid _

/-- Exact native range matching bounds the outgoing PC before decoder use. -/
theorem final_pc_low
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .subwordMemoryCached group index.val) input) : (inputRow input).finish.word.lo < 65536 := by
  change ((Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment input.physical
    (fun _ _ => #[])).get Airbender.SubwordMemory.importedConstraintsTraceColumns.finalPC[0]).val < 65536
  simpa [Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.rangeExpression3, _root_.Expression.eval,
    Airbender.SubwordMemory.importedConstraintsTraceColumns, Arithmetic.limbBase] using
    Verification.range16_bound (final_range_lookup decoder wordAt input arguments (fun _ _ => #[]))

end Airbender.Compiler.ProgramPCLowNative.SubwordMemoryCached
