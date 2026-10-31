import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.AddSubUncached

namespace Airbender.Compiler.ProgramConstraintsNative.AddSubUncached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.AddSubUncached
set_option warningAsError true
set_option Elab.async false

private theorem range_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.AddSubUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field0_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.AddSubUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field1_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value1 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := ProgramFixedLookup.AddSubUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field2_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value2 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨3, by decide⟩
  have member := ProgramFixedLookup.AddSubUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field3_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value3 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup4
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨4, by decide⟩
  have member := ProgramFixedLookup.AddSubUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field4_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value4 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup5
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries.get ⟨5, by decide⟩
  have member := ProgramFixedLookup.AddSubUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.AddSubUncached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.range_value5 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.AddSubUncached.native.range16_clean_refinement _ valid _

/-- Native ADD/SUB constraints hold for any public program setup rows. -/
theorem input_constraints
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input) (setup : Trace.PooledSetup babyBearModulus) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints setup) := by
  have helpers := ProgramFixedLookup.AddSubUncached.helpers_from_arguments decoder wordAt input arguments
  apply Airbender.Compiler.CleanLinksNative.AddSubUncached.retained_clock_constraints input.physical (fun _ _ => #[]) input.arithmetic
  rw [Airbender.Compiler.PhysicalClosedNative.AddSubUncached.clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup1 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup2 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup3 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup4 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup5 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound0 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound1 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound2 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound3 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound4 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound5 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound6 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestamp_bound7 input.physical (fun _ _ => #[]) input.arithmetic helpers)) PredicateChecks.nil))))))))))))))

end Airbender.Compiler.ProgramConstraintsNative.AddSubUncached
