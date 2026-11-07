import Airbender.Review.Circuits.ReducedMachine.CSR
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimePool
import Airbender.Proofs.Constraints
import Mathlib.Tactic.FinCases

namespace Airbender.ReducedMachine.NativeCSRPositiveWitness
open Native Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Independently constructed full body for CSRRW x0,1991,x0 at PC0/time4.
    All three x0 ports alias: old timestamps0,4,5; refreshes4,5,6. The execute
    observation varies alone. This is not a full physical/global proof witness. -/
def values : Array Nat := #[
    0,0,4,0,1,0,0,0,1,1991,0,1,129,4,0,8,
    0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1991,
    0,4,0,1227138194,0,2147450879,0,0,0,0,0,0,0,0,0,0,
    1,1,0,0,1,0,0,0,0,4,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,1,1,0,0,1,0,1991,0,
    0,0,0,0,1991,1,1,25,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,1,4,0,1,5,0,1,0
  ]

def assignment (active : Bool) (column : Nat) : ZMod mersenne31Modulus :=
  if column = 4 then (if active then 1 else 0) else ((values[column]?).getD 0 : Nat)

private theorem sign_zero : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
    (#v[0,0,0,16] : Vector (ZMod mersenne31Modulus) 4) := by
  refine ⟨⟨196609,by decide⟩,?_⟩
  decide +kernel

private theorem csr_member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
    (#v[1991,1,1,25] : Vector (ZMod mersenne31Modulus) 4) := by
  refine ⟨⟨1509576,by decide⟩,?_⟩
  decide +kernel

private theorem zero_member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
    (#v[0,0,0,0] : Vector (ZMod mersenne31Modulus) 4) := by
  refine ⟨⟨0,by decide⟩,?_⟩
  decide +kernel

private def polynomialValue (active : Bool) (i : Fin 117) : ZMod mersenne31Modulus :=
  ((FlatOperation.constraints (importedConstraints NativeRuntimePool.table)).get i).eval
    (environment (assignment active))

private theorem polynomials0 (active : Bool) (i : Fin 32) :
    polynomialValue active ⟨0 + i.val,by omega⟩ = 0 := by
  cases active <;> fin_cases i <;> decide +kernel

private theorem polynomials1 (active : Bool) (i : Fin 32) :
    polynomialValue active ⟨32 + i.val,by omega⟩ = 0 := by
  cases active <;> fin_cases i <;> decide +kernel

private theorem polynomials2 (active : Bool) (i : Fin 32) :
    polynomialValue active ⟨64 + i.val,by omega⟩ = 0 := by
  cases active <;> fin_cases i <;> decide +kernel

private theorem polynomials3 (active : Bool) (i : Fin 21) :
    polynomialValue active ⟨96 + i.val,by omega⟩ = 0 := by
  cases active <;> fin_cases i <;> decide +kernel


private theorem polynomials (active : Bool) (i : Fin 117) : polynomialValue active i = 0 := by
  rcases i with ⟨i,bound⟩
  by_cases h0 : i < 32
  · simpa only [Nat.zero_add] using polynomials0 active ⟨i,h0⟩
  by_cases h1 : i < 64
  · have key : 32 + (i - 32) = i := by omega
    simpa only [key] using polynomials1 active ⟨i - 32,by omega⟩
  by_cases h2 : i < 96
  · have key : 64 + (i - 64) = i := by omega
    simpa only [key] using polynomials2 active ⟨i - 64,by omega⟩
  · have key : 96 + (i - 96) = i := by omega
    simpa only [key] using polynomials3 active ⟨i - 96,by omega⟩

private theorem lookups (active : Bool) (i : Fin 22) :
    ((FlatOperation.lookups (importedConstraints NativeRuntimePool.table)).get i).Contains
      (environment (assignment active)) := by
  cases active <;> fin_cases i
  all_goals first
    | (apply range16_contains; decide +kernel)
    | (apply timestamp19_contains; decide +kernel)
    | skip
  all_goals first
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using sign_zero)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using csr_member)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using zero_member)

/-- Every117 native equation and all22 lookups on the complete actual runtime
    pool, for BOTH execute observations. No partial polynomial slice is used. -/
theorem body (active : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment active))
    (importedConstraints NativeRuntimePool.table) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · intro expression member
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact polynomials active ⟨i.val,i.isLt⟩
  · intro lookup member
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact lookups active ⟨i.val,i.isLt⟩

end Airbender.ReducedMachine.NativeCSRPositiveWitness
