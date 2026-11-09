import Airbender.Proofs.ReducedMachine.PointerPrefix.Data

namespace Airbender.NativePointerPrefixProofs.Block7
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

def index (row : Fin 4) : Fin 41 := ⟨28 + row.val,by have := row.isLt; omega⟩

private theorem sign_zero : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
    (#v[0,0,0,16] : Vector F 4) := by
  refine ⟨⟨196609,by decide⟩,?_⟩
  decide +kernel

private theorem zero_member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
    (#v[0,0,0,0] : Vector F 4) := by
  refine ⟨⟨0,by decide⟩,?_⟩
  decide +kernel

private def polynomialValue (row : Fin 4) (i : Fin 117) : F :=
  ((FlatOperation.constraints (importedConstraints NativeRuntimePool.table)).get i).eval (environment (assignment (index row)))

private theorem polynomials0 (row : Fin 4) (i : Fin 32) : polynomialValue row ⟨i.val,by omega⟩ = 0 := by
  fin_cases row <;> fin_cases i <;> decide +kernel
private theorem polynomials1 (row : Fin 4) (i : Fin 32) : polynomialValue row ⟨32 + i.val,by omega⟩ = 0 := by
  fin_cases row <;> fin_cases i <;> decide +kernel
private theorem polynomials2 (row : Fin 4) (i : Fin 32) : polynomialValue row ⟨64 + i.val,by omega⟩ = 0 := by
  fin_cases row <;> fin_cases i <;> decide +kernel
private theorem polynomials3 (row : Fin 4) (i : Fin 21) : polynomialValue row ⟨96 + i.val,by omega⟩ = 0 := by
  fin_cases row <;> fin_cases i <;> decide +kernel

private theorem polynomials (row : Fin 4) (i : Fin 117) : polynomialValue row i = 0 := by
  rcases i with ⟨i,bound⟩
  by_cases h0 : i < 32
  · exact polynomials0 row ⟨i,h0⟩
  by_cases h1 : i < 64
  · have key : 32 + (i - 32) = i := by omega
    simpa only [key] using polynomials1 row ⟨i - 32,by omega⟩
  by_cases h2 : i < 96
  · have key : 64 + (i - 64) = i := by omega
    simpa only [key] using polynomials2 row ⟨i - 64,by omega⟩
  · have key : 96 + (i - 96) = i := by omega
    simpa only [key] using polynomials3 row ⟨i - 96,by omega⟩

private theorem lookups0 (i : Fin 22) :
    ((FlatOperation.lookups (importedConstraints NativeRuntimePool.table)).get i).Contains (environment (assignment (index 0))) := by
  fin_cases i
  all_goals first
    | (apply range16_contains; decide +kernel)
    | (apply timestamp19_contains; decide +kernel)
    | skip
  all_goals first
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,index,baseValues,pcInverses,ramAddress,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using sign_zero)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,index,baseValues,pcInverses,ramAddress,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using zero_member)

private theorem lookups1 (i : Fin 22) :
    ((FlatOperation.lookups (importedConstraints NativeRuntimePool.table)).get i).Contains (environment (assignment (index 1))) := by
  fin_cases i
  all_goals first
    | (apply range16_contains; decide +kernel)
    | (apply timestamp19_contains; decide +kernel)
    | skip
  all_goals first
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,index,baseValues,pcInverses,ramAddress,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using sign_zero)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,index,baseValues,pcInverses,ramAddress,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using zero_member)

private theorem lookups2 (i : Fin 22) :
    ((FlatOperation.lookups (importedConstraints NativeRuntimePool.table)).get i).Contains (environment (assignment (index 2))) := by
  fin_cases i
  all_goals first
    | (apply range16_contains; decide +kernel)
    | (apply timestamp19_contains; decide +kernel)
    | skip
  all_goals first
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,index,baseValues,pcInverses,ramAddress,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using sign_zero)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,index,baseValues,pcInverses,ramAddress,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using zero_member)

private theorem lookups3 (i : Fin 22) :
    ((FlatOperation.lookups (importedConstraints NativeRuntimePool.table)).get i).Contains (environment (assignment (index 3))) := by
  fin_cases i
  all_goals first
    | (apply range16_contains; decide +kernel)
    | (apply timestamp19_contains; decide +kernel)
    | skip
  all_goals first
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,index,baseValues,pcInverses,ramAddress,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using sign_zero)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,index,baseValues,pcInverses,ramAddress,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using zero_member)

private theorem lookups (row : Fin 4) (i : Fin 22) :
    ((FlatOperation.lookups (importedConstraints NativeRuntimePool.table)).get i).Contains (environment (assignment (index row))) := by
  fin_cases row
  · exact lookups0 i
  · exact lookups1 i
  · exact lookups2 i
  · exact lookups3 i

theorem body (row : Fin 4) : FlatOperation.ConstraintsHoldFlat (environment (assignment (index row))) (importedConstraints NativeRuntimePool.table) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · intro expression member
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact polynomials row ⟨i.val,i.isLt⟩
  · intro lookup member
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact lookups row ⟨i.val,i.isLt⟩

end Airbender.NativePointerPrefixProofs.Block7
