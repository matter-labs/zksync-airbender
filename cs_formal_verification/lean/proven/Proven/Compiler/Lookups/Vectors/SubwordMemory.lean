module
public import Proven.Compiler.FixedMembership
public import Proven.Compiler.Lookups.Clean
public import Proven.Compiler.Lookups.Source.SubwordMemory
public import Proven.GKRProtocol.CleanGenericArgumentsNative.SubwordMemoryCached

@[expose] public section
namespace Airbender.Compiler.NativeVectorLookups.SubwordMemory
open Airbender Airbender.Compiler Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 65536

/-- Enabled generic tuples match independently interpreted native setup rows. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory)))
    (query : SourceLookupQuery) (member : query ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries)
    (enabled : query.weight (RingHom.id _)
      ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 0
      (query.fields.map (fun field => field.value
        ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement))) := by
  apply NativeSourceTransport.SubwordMemory.source_member arithmetic arguments 0
    (query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘
      Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)) ?_ enabled
  simpa [NativeSourceTransport.SubwordMemory.sourceRequests] using
    (List.mem_map.mpr ⟨query, member, rfl⟩ : query.materialized _ ∈
      Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries.map
        (fun entry => entry.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)))

theorem generic_lookup0
    (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    (Lookup.mk (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial)).toRaw Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries.get ⟨0, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value0_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value0_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value0_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value0_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value0_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value0_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value0_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value0_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value0_8 physical data arithmetic)
  apply clean_vector_lookup
  apply NativeFixedMembership.subword_contains bound _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
    change NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 0 [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) = 0
    rw [same7]
    rfl


theorem generic_lookup1
    (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    (Lookup.mk (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial)).toRaw Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.genericExpressions1).Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries.get ⟨1, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value1_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value1_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value1_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value1_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value1_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value1_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value1_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value1_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.generic_value1_8 physical data arithmetic)
  apply clean_vector_lookup
  apply NativeFixedMembership.subword_contains bound _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
    change NativePublicSetup.Proofs.Contains initial program (.pooled .subwordMemory) 0 [Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_0.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_1.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_2.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_3.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_4.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_5.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_6.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_7.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.part0.genericExpression1_7.eval (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) = 0
    rw [same7]
    rfl

end Airbender.Compiler.NativeVectorLookups.SubwordMemory
