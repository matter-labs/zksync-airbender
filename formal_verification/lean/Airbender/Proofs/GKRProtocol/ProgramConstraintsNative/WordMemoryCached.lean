import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.WordMemoryCached
import Airbender.Proofs.GKRProtocol.ProgramWordROM
import Airbender.Proofs.GKRProtocol.ProgramWordTags

namespace Airbender.Compiler.ProgramConstraintsNative.WordMemoryCached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.WordMemoryCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

private theorem range_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .wordMemoryCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.WordMemoryCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.WordMemoryCached.native.field1_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.WordMemoryCached.native.range16_clean_refinement _ valid _

private theorem range_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .wordMemoryCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.WordMemoryCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.WordMemoryCached.native.field2_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.range_value1 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.WordMemoryCached.native.range16_clean_refinement _ valid _

private theorem range_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .wordMemoryCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries.get ⟨2, by decide⟩
  have member := ProgramFixedLookup.WordMemoryCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.WordMemoryCached.native.field3_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.range_value2 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.WordMemoryCached.native.range16_clean_refinement _ valid _

private theorem generic_lookup0
    {initial : Reference.RiscV.Sail.State}
    (decoder : Configuration → List (List Source.BaseField)) (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.rows decoder (Trace.ROM.words initial) .wordMemoryCached group index.val) input)
    {cells : List Trace.Cell} {tokens : List (Trace.MemoryToken babyBearModulus)}
    (image : Trace.initialImage initial cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) (notDecoder : (inputRow input).assignment 45 ≠ 46)
    (data : ProverData Source.BaseField) :
    (Lookup.mk (Trace.ROM.table cells tokens).toRaw Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.genericExpressions0).Contains
      (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.get ⟨0, by decide⟩
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.rows decoder (Trace.ROM.words initial) .wordMemoryCached group index.val) input arguments 0
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement))
    (List.mem_map.mpr ⟨query, List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries ⟨0, by decide⟩, rfl⟩)
    one_ne_zero
  have same0 := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_0 input.physical data input.arithmetic
  have same1 := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_1 input.physical data input.arithmetic
  have same2 := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_2 input.physical data input.arithmetic
  have same3 := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_3 input.physical data input.arithmetic
  have same4 := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_4 input.physical data input.arithmetic
  have same5 := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_5 input.physical data input.arithmetic
  have same6 := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_6 input.physical data input.arithmetic
  have same7 := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_7 input.physical data input.arithmetic
  have same8 := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_8 input.physical data input.arithmetic
  let actual := Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.genericExpressions0.map
    (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data))
  have guard : actual[8] ≠ 46 := by
    simp [actual, Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.genericExpressions0,
      Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_8, _root_.Expression.eval]
    change (inputRow input).assignment 45 ≠ 46
    exact notDecoder
  apply clean_vector_lookup
  apply NativeProgramSetup.word_public_member image domain decoder .wordMemoryCached
    (Or.inr rfl) nativeIndex actual ?_ guard
  simp only [actual, Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
  change [(Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_0).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_1).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_2).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_3).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_4).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_5).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_6).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_7).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_8).eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical data)] = _
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact matched

private theorem clock_lookup_inventory (rom : Table Source.BaseField (fields 9)) :
    FlatOperation.lookups (Airbender.WordMemory.clockConstraints (p := babyBearModulus) rom) =
    (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.genericExpressions.map (fun entry => Lookup.mk rom.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

/-- Exact native matching proves word-memory constraints for the public image. -/
theorem input_constraints
    {initial : Reference.RiscV.Sail.State}
    (decoder : Configuration → List (List Source.BaseField)) (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.rows decoder (Trace.ROM.words initial) .wordMemoryCached group index.val) input)
    {cells : List Trace.Cell} {tokens : List (Trace.MemoryToken babyBearModulus)}
    (image : Trace.initialImage initial cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) (subwordSetup : Table Source.BaseField (fields 9)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨Trace.ROM.table cells tokens, subwordSetup⟩ : Trace.PooledSetup babyBearModulus)) := by
  have helpers := ProgramFixedLookup.WordMemoryCached.helpers_from_arguments decoder (Trace.ROM.words initial) input arguments
  have assertions : ∀ expression ∈ FlatOperation.constraints (WordMemory.importedConstraints (Trace.ROM.table cells tokens)),
      expression.eval (Verification.environment (inputRow input).assignment) = 0 := by
    rw [Airbender.Compiler.CleanLinksNative.WordMemoryCached.arithmetic_inventory]
    exact CleanExpression.assertions_only _ _
      (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.arithmetic_preserved input.physical (fun _ _ => #[]) input.arithmetic)
  have notDecoder := word_helper_not_decoder _ _ assertions
  apply Airbender.Compiler.CleanLinksNative.WordMemoryCached.retained_clock_constraints (Trace.ROM.table cells tokens) input.physical (fun _ _ => #[]) input.arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 decoder (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup1 decoder (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup2 decoder (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup0 decoder input arguments image domain notDecoder (fun _ _ => #[])) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound0 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound1 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound2 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound3 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound4 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound5 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound6 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound7 input.physical (fun _ _ => #[]) input.arithmetic helpers)) PredicateChecks.nil))))))))))))

end Airbender.Compiler.ProgramConstraintsNative.WordMemoryCached
