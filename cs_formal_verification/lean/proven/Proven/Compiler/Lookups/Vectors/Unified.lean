module
public import Proven.Compiler.FixedMembership
public import Proven.Compiler.Lookups.Clean
public import Proven.Compiler.Lookups.Source.Unified
public import Proven.GKRProtocol.CleanGenericArgumentsNative.UnifiedCached

@[expose] public section
namespace Airbender.Compiler.NativeVectorLookups.Unified
open Airbender Airbender.Compiler Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 65536

/-- Enabled generic tuples match independently interpreted native setup rows. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (NativePublicSetup.rows initial program .unified))
    (query : SourceLookupQuery) (member : query ∈ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries)
    (enabled : query.weight (RingHom.id _)
      ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ≠ 0) :
    NativePublicSetup.Proofs.Contains initial program .unified 0
      (query.fields.map (fun field => field.value
        ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement))) := by
  apply NativeSourceTransport.Unified.source_member arithmetic arguments 0
    (query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘
      Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)) ?_ enabled
  simpa [NativeSourceTransport.Unified.sourceRequests] using
    (List.mem_map.mpr ⟨query, member, rfl⟩ : query.materialized _ ∈
      Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.map
        (fun entry => entry.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement)))

theorem generic_lookup0
    (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (NativePublicSetup.rows initial program .unified)) :
    (Lookup.mk (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨0, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value0_9 physical data arithmetic)
  apply clean_vector_lookup
  apply NativeFixedMembership.unified_contains bound _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
    change NativePublicSetup.Proofs.Contains initial program .unified 0 [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) = 0
    rw [same8]
    rfl


theorem generic_lookup1
    (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (NativePublicSetup.rows initial program .unified)) :
    (Lookup.mk (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions1).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨1, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value1_9 physical data arithmetic)
  apply clean_vector_lookup
  apply NativeFixedMembership.unified_contains bound _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
    change NativePublicSetup.Proofs.Contains initial program .unified 0 [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) = 0
    rw [same8]
    rfl


theorem generic_lookup2
    (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (NativePublicSetup.rows initial program .unified)) :
    (Lookup.mk (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions2).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨2, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value2_9 physical data arithmetic)
  apply clean_vector_lookup
  apply NativeFixedMembership.unified_contains bound _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions2, Vector.map_mk, List.map_toArray]
    change NativePublicSetup.Proofs.Contains initial program .unified 0 [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression2_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) = 0
    rw [same8]
    rfl


theorem generic_lookup3
    (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (NativePublicSetup.rows initial program .unified)) :
    (Lookup.mk (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions3).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨3, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value3_9 physical data arithmetic)
  apply clean_vector_lookup
  apply NativeFixedMembership.unified_contains bound _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions3, Vector.map_mk, List.map_toArray]
    change NativePublicSetup.Proofs.Contains initial program .unified 0 [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression3_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) = 0
    rw [same8]
    rfl


theorem generic_lookup4
    (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (NativePublicSetup.rows initial program .unified)) :
    (Lookup.mk (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions4).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.get ⟨4, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_8 physical data arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.generic_value4_9 physical data arithmetic)
  apply clean_vector_lookup
  apply NativeFixedMembership.unified_contains bound _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions4, Vector.map_mk, List.map_toArray]
    change NativePublicSetup.Proofs.Contains initial program .unified 0 [Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_0.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_1.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_2.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_3.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_4.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_5.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_6.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_7.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_9.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.part0.genericExpression4_8.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) = 0
    rw [same8]
    rfl

end Airbender.Compiler.NativeVectorLookups.Unified
