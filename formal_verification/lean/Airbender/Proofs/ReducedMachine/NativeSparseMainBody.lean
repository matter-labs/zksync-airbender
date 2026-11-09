import Airbender.Review.Trace.Families.ReducedMachine.SparseMain
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.NativeSparseMainProofs
open Airbender.NativeSparseMain Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Verification
abbrev original : Nat → F := NativeCSRPositiveWitness.assignment false
abbrev idle : Nat → F := NativeSparseMain.idle original
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private theorem sign_zero : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
    (#v[0,0,0,16] : Vector F 4) := by
  refine ⟨⟨196609,by decide⟩,?_⟩
  decide +kernel

private theorem csr_member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
    (#v[1984,1,0,25] : Vector F 4) := by
  refine ⟨⟨1509569,by decide⟩,?_⟩
  decide +kernel

private theorem zero_member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
    (#v[0,0,0,0] : Vector F 4) := by
  refine ⟨⟨0,by decide⟩,?_⟩
  decide +kernel

private def polynomialValue (i : Fin 117) : F :=
  ((FlatOperation.constraints (importedConstraints NativeRuntimePool.table)).get i).eval (environment idle)

private theorem polynomials0 (i : Fin 32) : polynomialValue ⟨i.val,by omega⟩ = 0 := by
  fin_cases i <;> decide +kernel
private theorem polynomials1 (i : Fin 32) : polynomialValue ⟨32 + i.val,by omega⟩ = 0 := by
  fin_cases i <;> decide +kernel
private theorem polynomials2 (i : Fin 32) : polynomialValue ⟨64 + i.val,by omega⟩ = 0 := by
  fin_cases i <;> decide +kernel
private theorem polynomials3 (i : Fin 21) : polynomialValue ⟨96 + i.val,by omega⟩ = 0 := by
  fin_cases i <;> decide +kernel

private theorem polynomials (i : Fin 117) : polynomialValue i = 0 := by
  rcases i with ⟨i,bound⟩
  by_cases h0 : i < 32
  · exact polynomials0 ⟨i,h0⟩
  by_cases h1 : i < 64
  · have key : 32 + (i - 32) = i := by omega
    simpa only [key] using polynomials1 ⟨i - 32,by omega⟩
  by_cases h2 : i < 96
  · have key : 64 + (i - 64) = i := by omega
    simpa only [key] using polynomials2 ⟨i - 64,by omega⟩
  · have key : 96 + (i - 96) = i := by omega
    simpa only [key] using polynomials3 ⟨i - 96,by omega⟩

private theorem lookups (i : Fin 22) :
    ((FlatOperation.lookups (importedConstraints NativeRuntimePool.table)).get i).Contains (environment idle) := by
  fin_cases i
  all_goals first
    | (apply range16_contains; decide +kernel)
    | (apply timestamp19_contains; decide +kernel)
    | skip
  all_goals first
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,idle,NativeSparseMain.idle,original,Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using sign_zero)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,idle,NativeSparseMain.idle,original,Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using csr_member)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,idle,NativeSparseMain.idle,original,Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment,
        Airbender.ReducedMachine.NativeCSRPositiveWitness.values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using zero_member)

theorem idle_body : FlatOperation.ConstraintsHoldFlat (environment idle) (importedConstraints NativeRuntimePool.table) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · intro expression member
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact polynomials ⟨i.val,i.isLt⟩
  · intro lookup member
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact lookups ⟨i.val,i.isLt⟩
end Airbender.NativeSparseMainProofs
