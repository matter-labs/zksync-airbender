module
public import Proven.Compiler.Lookups.Clean
public import Proven.Compiler.Lookups.NativeRanges
public import Proven.Compiler.Lookups.Source.WordMemory
public import Proven.GKRProtocol.CleanGenericArgumentsNative.WordMemoryCached
public import Proven.Compiler.ROMMembership

@[expose] public section
namespace Airbender.Compiler.NativeVectorLookups.WordMemory
open Airbender Airbender.Compiler Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 65536

/-- Enabled source range tuples match complete independent native setup rows. -/
theorem member (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .wordMemory))
      (NativeLookups.selectorsFor (.pooled .wordMemory)) physical (NativePublicSetup.rows initial program (.pooled .wordMemory)))
    (query : SourceLookupQuery) (member : query ∈ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries)
    (enabled : query.weight (RingHom.id _)
      ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ≠ 0) :
    NativePublicSetup.Proofs.Contains initial program (.pooled .wordMemory) 0
      (query.fields.map (fun field => field.value
        ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘
          Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement))) := by
  apply NativeSourceTransport.WordMemory.source_member arithmetic arguments 0
    (query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘
      Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)) ?_ enabled
  simpa [NativeSourceTransport.WordMemory.sourceRequests] using
    (List.mem_map.mpr ⟨query, member, rfl⟩ :
      query.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ∈
        Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.map
          (fun entry => entry.materialized ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)))

theorem generic_lookup0
    (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (cells : List Cell) (covers : NativePublicSetup.CoversROM cells)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .wordMemory))
      (NativeLookups.selectorsFor (.pooled .wordMemory)) physical (NativePublicSetup.rows initial program (.pooled .wordMemory))) :
    (Lookup.mk (ROM.table (p := babyBearModulus) cells (romImageRV initial cells)).toRaw Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.get ⟨0, by decide⟩
  have member := member initial program physical arithmetic arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_0 physical data arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_1 physical data arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_2 physical data arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_3 physical data arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_4 physical data arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_5 physical data arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_6 physical data arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_7 physical data arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.generic_value0_8 physical data arithmetic)
  apply clean_vector_lookup
  apply NativeFixedMembership.word_contains bound cells covers _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
    change NativePublicSetup.Proofs.Contains initial program (.pooled .wordMemory) 0 [Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data), Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) = 0
    rw [same7]
    rfl

end Airbender.Compiler.NativeVectorLookups.WordMemory
