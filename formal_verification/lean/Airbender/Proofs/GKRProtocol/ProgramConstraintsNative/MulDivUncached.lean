import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.MulDivUncached

namespace Airbender.Compiler.ProgramConstraintsNative.MulDivUncached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.MulDivUncached
open Airbender.Compiler.PhysicalClosedNative.MulDivUncached
set_option warningAsError true
set_option Elab.async false

private theorem range_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivUncached.native.field8_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivUncached.native.field9_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.range_value1 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivUncached.native.field10_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.range_value2 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries.get ⟨3, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivUncached.native.field11_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.range_value3 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup4
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries.get ⟨4, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivUncached.native.field12_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.range_value4 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup5
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries.get ⟨5, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivUncached.native.field13_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.range_value5 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup6
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.rangeExpression6).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries.get ⟨6, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivUncached.native.field14_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.range_value6 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup7
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.rangeExpression7).Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries.get ⟨7, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.MulDivUncached.native.field15_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.range_value7 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.MulDivUncached.native.range16_clean_refinement _ valid _

private theorem generic_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup0.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨0, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (1 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 1 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field0_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value0_0 input.physical data input.arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field0_1.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value0_1 input.physical data input.arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag1_contains setupRow selected _


private theorem generic_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup1.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨1, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 41 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field1_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value1_0 input.physical data input.arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field1_1.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value1_1 input.physical data input.arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag41_contains setupRow selected _


private theorem generic_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup2.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.get ⟨2, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨2, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 41 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field2_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value2_0 input.physical data input.arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field2_1.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value2_1 input.physical data input.arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag41_contains setupRow selected _


private theorem generic_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup3.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.get ⟨3, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨3, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (26 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 26 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field3_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value3_0 input.physical data input.arithmetic).trans sourceCell0
  apply Verification.range13_contains
  rw [same0]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.range13_value_bound setupRow selected


private theorem generic_lookup4
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup4.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.get ⟨4, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨4, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (26 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 26 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field4_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value4_0 input.physical data input.arithmetic).trans sourceCell0
  apply Verification.range13_contains
  rw [same0]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.range13_value_bound setupRow selected


private theorem generic_lookup5
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup5.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.get ⟨5, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨5, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (26 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 26 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value5_0 input.physical data input.arithmetic).trans sourceCell0
  apply Verification.range13_contains
  rw [same0]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.range13_value_bound setupRow selected


private theorem generic_lookup6
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup6.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.get ⟨6, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨6, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 41 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field6_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value6_0 input.physical data input.arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field6_1.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value6_1 input.physical data input.arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag41_contains setupRow selected _


private theorem generic_lookup7
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (data : ProverData Source.BaseField) :
    fixedLookup7.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.get ⟨7, by decide⟩
  have member := ProgramFixedLookup.MulDivUncached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ⟨7, by decide⟩) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  obtain ⟨setupRow, dataRow⟩ := member nonzero
  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD 8 0) dataRow
  change (41 : Source.BaseField) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 8) at tagProof
  have selected : Airbender.Compiler.FixedSetupNative.MulDiv.nativeSetup.value setupRow (.generic 8) = 41 := tagProof.symm
  have sourceCell0 := congrArg (fun entries : List Source.BaseField => entries.getD 0 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field7_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 0) at sourceCell0
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value7_0 input.physical data input.arithmetic).trans sourceCell0
  have sourceCell1 := congrArg (fun entries : List Source.BaseField => entries.getD 1 0) dataRow
  change Airbender.Compiler.LookupNative.MulDivUncached.native.field7_1.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) = Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.value setupRow (.generic 1) at sourceCell1
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native.part0.generic_value7_1 input.physical data input.arithmetic).trans sourceCell1
  apply clean_pair_lookup
  rw [same0, same1]
  exact Airbender.Compiler.FixedSetupNative.MulDiv.tag41_contains setupRow selected _


/-- Native CPU constraints hold for any public program setup rows. -/
theorem input_constraints
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .mulDivUncached group index.val) input) (setup : Trace.PooledSetup babyBearModulus) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints setup) := by
  have helpers := ProgramFixedLookup.MulDivUncached.helpers_from_arguments decoder wordAt input arguments
  apply Airbender.Compiler.CleanLinksNative.MulDivUncached.retained_clock_constraints input.physical (fun _ _ => #[]) input.arithmetic
  rw [Airbender.Compiler.PhysicalClosedNative.MulDivUncached.clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup1 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup2 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup3 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup4 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup5 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup6 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup7 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup0 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup1 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup2 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup3 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup4 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup5 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup6 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup7 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestamp_bound0 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestamp_bound1 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestamp_bound2 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestamp_bound3 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestamp_bound4 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestamp_bound5 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestamp_bound6 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.MulDivUncached.native.timestamp_bound7 input.physical (fun _ _ => #[]) input.arithmetic helpers)) PredicateChecks.nil))))))))))))))))))))))))

end Airbender.Compiler.ProgramConstraintsNative.MulDivUncached
