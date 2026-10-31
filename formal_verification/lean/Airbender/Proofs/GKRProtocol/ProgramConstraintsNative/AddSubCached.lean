import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.AddSubCached

namespace Airbender.Compiler.ProgramConstraintsNative.AddSubCached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.AddSubCached
set_option warningAsError true
set_option Elab.async false

private theorem range_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.AddSubCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field0_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

private theorem range_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.AddSubCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field1_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value1 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

private theorem range_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨2, by decide⟩
  have member := ProgramFixedLookup.AddSubCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field2_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value2 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

private theorem range_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨3, by decide⟩
  have member := ProgramFixedLookup.AddSubCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field3_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value3 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

private theorem range_lookup4
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨4, by decide⟩
  have member := ProgramFixedLookup.AddSubCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field4_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value4 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

private theorem range_lookup5
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.get ⟨5, by decide⟩
  have member := ProgramFixedLookup.AddSubCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubCached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.range_value5 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubCached.native.range16_clean_refinement _ valid _

/-- Native ADD/SUB constraints hold for any public program setup rows. -/
theorem input_constraints
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubCached group index.val) input) (setup : Trace.PooledSetup babyBearModulus) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints setup) := by
  have helpers := ProgramFixedLookup.AddSubCached.helpers_from_arguments decoder wordAt input arguments
  apply Airbender.Compiler.CleanLinksNative.AddSubCached.retained_clock_constraints input.physical (fun _ _ => #[]) input.arithmetic
  rw [Airbender.Compiler.PhysicalClosedNative.AddSubCached.clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup1 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup2 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup3 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup4 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup5 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound0 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound1 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound2 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound3 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound4 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound5 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound6 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound7 input.physical (fun _ _ => #[]) input.arithmetic helpers)) PredicateChecks.nil))))))))))))))

end Airbender.Compiler.ProgramConstraintsNative.AddSubCached
