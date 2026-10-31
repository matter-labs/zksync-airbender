import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.ProgramSubwordSetup
import Airbender.Proofs.GKRProtocol.ProgramSubwordTags
import Airbender.Proofs.GKRProtocol.ProgramSubwordDecoder
import Airbender.Proofs.GKRProtocol.ProgramDecoderNative.SubwordMemoryUncached
import Airbender.Proofs.Tables.DecoderPCLow

namespace Airbender.Compiler.ProgramConstraintsNative.SubwordMemoryUncached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

/-- Range and timestamp matching use the unchanged native setup groups. -/
private theorem fixed_group_member
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input)
    (group : Fin 3) (other : group.val ≠ 0) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains (Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.setupColumns group) query.fields := by
  obtain ⟨index, equal⟩ := source_member_with (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val)
    input arguments group query member enabled
  rw [NativeProgramSetup.program_rows_fixed_group decoder wordAt .subwordMemoryUncached group index.val other] at equal
  refine ⟨index, ?_⟩
  simpa only [NativeProgramSetup.retainedRows, dif_pos index.isLt, Airbender.Compiler.MaterializedWitnessNative.SubwordMemoryUncached.setupColumns] using equal

private theorem range_from_arguments
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) :
    ∀ query ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries,
      query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 →
        Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.range16SetupColumns
          (query.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))) := by
  intro query member enabled
  apply fixed_group_member decoder wordAt input arguments 1 (by decide +kernel)
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)) ?_ enabled
  exact List.mem_map.mpr ⟨query, member, rfl⟩

private theorem helpers_from_arguments (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)
  have present := fixed_group_member decoder wordAt input arguments 2 (by decide +kernel) (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.SubwordMemoryUncached.native.timestamp_bounded value present

private theorem range_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field2_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field3_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value1 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field4_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value2 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨3, by decide⟩
  have member := range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value3 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup4
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.get ⟨4, by decide⟩
  have member := range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.field6_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.range_value4 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.SubwordMemoryUncached.native.range16_clean_refinement _ valid _

private theorem generic_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) (_notDecoder : (inputRow input).assignment 61 ≠ 46)
    (data : ProverData Source.BaseField) :
    (Lookup.mk (Verification.subwordTable wordAt).toRaw Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions0).Contains
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.get ⟨0, by decide⟩
  have tagSame : (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_8).eval
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data) =
      (query.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))).getLast?.getD 0 :=
    Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_8 input.physical data input.arithmetic
  have guard : (query.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))).getLast?.getD 0 ≠ 46 := by
    rw [← tagSame]
    simp [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_8, _root_.Expression.eval]
    exact of_decide_eq_true rfl
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input arguments 0
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))
    (List.mem_map.mpr ⟨query, List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries ⟨0, by decide⟩, rfl⟩)
    one_ne_zero
  have matchedRow : (query.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))) =
      NativeProgramSetup.subwordRows (decoder .subwordMemoryUncached) wordAt nativeIndex.val := by
    simpa [NativeProgramSetup.programRows, SourceLookupQuery.materialized] using matched
  obtain ⟨row, equal⟩ := NativeProgramSetup.subword_query_member (decoder .subwordMemoryUncached) wordAt
    nativeIndex.val _ matchedRow guard
  have same0 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_0 input.physical data input.arithmetic
  have same1 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_1 input.physical data input.arithmetic
  have same2 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_2 input.physical data input.arithmetic
  have same3 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_3 input.physical data input.arithmetic
  have same4 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_4 input.physical data input.arithmetic
  have same5 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_5 input.physical data input.arithmetic
  have same6 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_6 input.physical data input.arithmetic
  have same7 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_7 input.physical data input.arithmetic
  have same8 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value0_8 input.physical data input.arithmetic
  apply clean_vector_lookup
  refine ⟨row, ?_⟩
  apply Vector.toList_inj.mp
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
  change [(Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_0).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_1).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_2).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_3).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_4).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_5).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_6).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_7).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_8).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data)] = _
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact equal

private theorem generic_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) (notDecoder : (inputRow input).assignment 61 ≠ 46)
    (data : ProverData Source.BaseField) :
    (Lookup.mk (Verification.subwordTable wordAt).toRaw Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions1).Contains
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.get ⟨1, by decide⟩
  have tagSame : (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_8).eval
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data) =
      (query.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))).getLast?.getD 0 :=
    Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_8 input.physical data input.arithmetic
  have guard : (query.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))).getLast?.getD 0 ≠ 46 := by
    rw [← tagSame]
    simp [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_8, _root_.Expression.eval]
    exact notDecoder
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input arguments 0
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))
    (List.mem_map.mpr ⟨query, List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries ⟨1, by decide⟩, rfl⟩)
    one_ne_zero
  have matchedRow : (query.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))) =
      NativeProgramSetup.subwordRows (decoder .subwordMemoryUncached) wordAt nativeIndex.val := by
    simpa [NativeProgramSetup.programRows, SourceLookupQuery.materialized] using matched
  obtain ⟨row, equal⟩ := NativeProgramSetup.subword_query_member (decoder .subwordMemoryUncached) wordAt
    nativeIndex.val _ matchedRow guard
  have same0 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_0 input.physical data input.arithmetic
  have same1 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_1 input.physical data input.arithmetic
  have same2 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_2 input.physical data input.arithmetic
  have same3 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_3 input.physical data input.arithmetic
  have same4 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_4 input.physical data input.arithmetic
  have same5 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_5 input.physical data input.arithmetic
  have same6 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_6 input.physical data input.arithmetic
  have same7 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_7 input.physical data input.arithmetic
  have same8 := Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.generic_value1_8 input.physical data input.arithmetic
  apply clean_vector_lookup
  refine ⟨row, ?_⟩
  apply Vector.toList_inj.mp
  simp only [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
  change [(Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_0).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_1).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_2).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_3).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_4).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_5).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_6).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_7).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_8).eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical data)] = _
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
  exact equal

private theorem clock_lookup_inventory (wordAt : Nat → BitVec 32) :
    FlatOperation.lookups (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) (Verification.subwordTable wordAt)) =
    (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions.map (fun entry => Lookup.mk (Verification.subwordTable wordAt).toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

/-- Exact native matching proves subword constraints for the public ROM function. -/
theorem input_constraints
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) (wordSetup : Table Source.BaseField (fields 9)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (⟨wordSetup, Verification.subwordTable wordAt⟩ : Trace.PooledSetup babyBearModulus)) := by
  have helpers := helpers_from_arguments decoder wordAt input arguments
  have assertions : ∀ expression ∈ FlatOperation.constraints (SubwordMemory.importedConstraints (Verification.subwordTable wordAt)),
      expression.eval (Verification.environment (inputRow input).assignment) = 0 := by
    rw [Airbender.Compiler.CleanLinksNative.SubwordMemoryUncached.arithmetic_inventory]
    exact CleanExpression.assertions_only _ _
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.arithmetic_preserved input.physical (fun _ _ => #[]) input.arithmetic)
  have notDecoder := subword_helper_not_decoder _ _ assertions
  apply Airbender.Compiler.CleanLinksNative.SubwordMemoryUncached.retained_clock_constraints (Verification.subwordTable wordAt) input.physical (fun _ _ => #[]) input.arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup1 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup2 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup3 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup4 decoder wordAt input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup0 decoder wordAt input arguments notDecoder (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup1 decoder wordAt input arguments notDecoder (fun _ _ => #[])) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound0 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound1 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound2 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound3 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound4 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound5 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound6 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryUncached.native.timestamp_bound7 input.physical (fun _ _ => #[]) input.arithmetic helpers)) PredicateChecks.nil)))))))))))))))


/-- Native range matching bounds the outgoing PC for the complete program factory. -/
theorem final_pc_low
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.programRows decoder wordAt .subwordMemoryUncached group index.val) input) : (inputRow input).finish.word.lo < 65536 :=
  Trace.NativeDecoder.Proofs.pooled_final_pc_low (by decide +kernel) (inputRow input)
    (⟨Verification.subwordTable wordAt, Verification.subwordTable wordAt⟩ : Trace.PooledSetup babyBearModulus)
    (input_constraints decoder wordAt input arguments (Verification.subwordTable wordAt))

/-- Exact native decoder matching uses the complete public subword setup. -/
theorem decoder_lookup
    {config : Trace.NativeDecoder.ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat}
    {masks : Trace.PooledFamily → Trace.NativeDecoder.ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.unrolledProgramLookupRows initial columns .subwordMemoryUncached group index.val) input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    Trace.NativeDecoder.ProgramRows.maskRow (masks .subwordMemory) (inputRow input).decoderQuery ∈ columns .subwordMemory := by
  obtain ⟨index, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.unrolledProgramLookupRows initial columns .subwordMemoryUncached group index.val)
    input arguments 0 (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))
    (ProgramDecoderNative.SubwordMemoryUncached.decoder_member input) (ProgramDecoderNative.SubwordMemoryUncached.decoder_enabled input)
  have equal : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.query12.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)) =
      NativeProgramSetup.unrolledProgramLookupRows initial columns .subwordMemoryUncached 0 index.val := matched
  apply NativeProgramSetup.unrolled_subword_decoder_lookup setup .subwordMemoryUncached
    (Or.inl rfl) index.val _ typed
  rw [NativeProgramSetup.unrolled_mask_eq setup .subwordMemory]
  exact (ProgramDecoderNative.SubwordMemoryUncached.decoder_tuple input).symm.trans equal

end Airbender.Compiler.ProgramConstraintsNative.SubwordMemoryUncached
