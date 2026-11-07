import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.JumpBranchCached

namespace Airbender.Compiler.ProgramConstraintsNative.JumpBranchCached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.JumpBranchCached
open Airbender.Compiler.PhysicalClosedNative.JumpBranchCached
set_option warningAsError true
set_option Elab.async false

private theorem range_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.JumpBranchCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchCached.native.field4_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchCached.native.range16_clean_refinement _ valid _

private theorem range_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.JumpBranchCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchCached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value1 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchCached.native.range16_clean_refinement _ valid _

private theorem range_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨2, by decide⟩
  have member := ProgramFixedLookup.JumpBranchCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchCached.native.field6_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value2 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchCached.native.range16_clean_refinement _ valid _

private theorem range_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.get ⟨3, by decide⟩
  have member := ProgramFixedLookup.JumpBranchCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.JumpBranchCached.native.field7_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.range_value3 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.JumpBranchCached.native.range16_clean_refinement _ valid _

private theorem generic_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup0.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.JumpBranchCached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨0, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (1 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 1 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field0_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value0_0 input.physical data input.arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field0_1.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value0_1 input.physical data input.arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag1_contains setupRow selected _


private theorem generic_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup1.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.JumpBranchCached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨1, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (5 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 5 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field1_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value1_0 input.physical data input.arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field1_1.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value1_1 input.physical data input.arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag5_contains setupRow selected _


private theorem generic_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup2.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨2, by decide⟩
  have member := ProgramFixedLookup.JumpBranchCached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨2, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (31 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 31 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field2_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value2_0 input.physical data input.arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field2_1.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value2_1 input.physical data input.arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag31_contains setupRow selected _


private theorem generic_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup3.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.get ⟨3, by decide⟩
  have member := ProgramFixedLookup.JumpBranchCached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ⟨3, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 9 0) dataRow
  change (2 : Source.BaseField) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 9) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.JumpBranch.nativeSetup.value setupRow (.generic 9) = 2 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field3_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value3_0 input.physical data input.arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field3_1.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value3_1 input.physical data input.arithmetic).trans sourceCell1
  have sourceCell2 := congrArg (fun entries : List Source.BaseField => entries.getD 2 0) dataRow
  change Airbender.Compiler.LookupNative.JumpBranchCached.native.field3_2.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.value setupRow (.generic 2) at sourceCell2
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native.part0.generic_value3_2 input.physical data input.arithmetic).trans sourceCell2
  apply clean_triple_lookup
  rw [same0, same1, same2]
  exact Airbender.Compiler.FixedSetupNative.JumpBranch.tag2_contains setupRow selected _


/-- Native CPU constraints hold for any public program setup rows. -/
theorem input_constraints
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (setup : Trace.PooledSetup babyBearModulus) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints setup) := by
  have helpers := ProgramFixedLookup.JumpBranchCached.helpers_from_arguments decoder wordAt input arguments
  apply Airbender.Compiler.CleanLinksNative.JumpBranchCached.retained_clock_constraints input.physical (fun _ _ => #[]) input.arithmetic
  rw [Airbender.Compiler.PhysicalClosedNative.JumpBranchCached.clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup1 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup2 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup3 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup0 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup1 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup2 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup3 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound0 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound1 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound2 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound3 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound4 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound5 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound6 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound7 input.physical (fun _ _ => #[]) input.arithmetic helpers)) PredicateChecks.nil))))))))))))))))

end Airbender.Compiler.ProgramConstraintsNative.JumpBranchCached
