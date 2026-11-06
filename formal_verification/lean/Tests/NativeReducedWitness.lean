import Airbender.Review.Trace.Families.ReducedMachine.FetchedExecution
import Airbender.Proofs.ReducedMachine.NativeShiftRows

namespace Tests.NativeReducedWitness
open Airbender Arithmetic Trace ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Independently constructed assignments for actual native SLL x3/x0,x1,x2,
-- with x1=x2=1. Original public PCs are0/48; candidate2 is retained in both.
def values (discarded : Bool) : Array Nat :=
  if discarded then #[
    48,0,4,0,1,1,2,0,1,0,0,1,4099,52,0,8,
    0,1,1,0,0,0,0,0,0,0,0,0,0,1,0,0,
    0,0,0,1,0,1,0,2,0,0,0,0,0,0,0,1,
    0,52,0,1603857167,0,2147450879,0,0,0,0,0,0,0,0,0,0,
    1,0,2,0,1,0,0,0,2,2147483595,0,0,0,2,0,0,
    0,1,0,1,0,0,0,0,1,1,0,0,0,0,0,0,
    0,0,0,0,1,1,0,47,65537,2,0,37,65536,0,0,37,
    4,0,0,20,2,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,1,0,0,1,0,0,1,0
  ] else #[
    0,0,4,0,1,1,2,3,0,0,0,1,4099,4,0,8,
    0,1,1,0,0,0,0,0,0,0,0,0,0,1,0,0,
    0,0,0,1,0,1,0,2,0,0,0,2,0,3,0,1,
    0,4,0,1227138194,0,2147450879,0,0,0,0,0,0,0,0,0,0,
    1,0,2,0,1,0,0,0,2,2147483643,0,0,0,2,0,0,
    0,1,0,1,0,0,0,0,1,1,0,0,0,0,0,0,
    0,0,0,0,1,1,0,47,65537,2,0,37,65536,0,0,37,
    4,0,0,20,2,0,2,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,1,0,0,1,0,0,1,0
  ]

def assignment (discarded : Bool) (column : Nat) : ZMod mersenne31Modulus :=
  ((values discarded)[column]?).getD 0

private theorem at_shift (n : Nat) (bound : n < 4194304) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      ((#v[n,(NativeFixed.shiftOutputs n)[0],(NativeFixed.shiftOutputs n)[1],37]).map
        (Nat.cast : Nat → ZMod mersenne31Modulus)) := by
  refine ⟨⟨n + 1511681,by change n + 1511681 < 5771521; omega⟩,?_⟩
  change _ = (NativeFixed.rowNat ⟨n + 1511681,_⟩).map Nat.cast
  have h0 : ¬ n + 1511681 < 1 := by omega
  have h1 : ¬ n + 1511681 < 65537 := by omega
  have h2 : ¬ n + 1511681 < 131073 := by omega
  have h3 : ¬ n + 1511681 < 196609 := by omega
  have h4 : ¬ n + 1511681 < 262145 := by omega
  have h5 : ¬ n + 1511681 < 327681 := by omega
  have h6 : ¬ n + 1511681 < 393217 := by omega
  have h7 : ¬ n + 1511681 < 393345 := by omega
  have h8 : ¬ n + 1511681 < 393473 := by omega
  have h9 : ¬ n + 1511681 < 459009 := by omega
  have h10 : ¬ n + 1511681 < 1507585 := by omega
  have h11 : ¬ n + 1511681 < 1511681 := by omega
  have selected : n + 1511681 < 5705985 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_neg h9,dif_neg h10,dif_neg h11,dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  rw [NativeShiftRowProofs.rows]


private theorem sign_zero : NativeFixed.table.Contains #[]
    (#v[0,0,0,16] : Vector (ZMod mersenne31Modulus) 4) := by
  refine ⟨⟨196609,by decide⟩,?_⟩
  decide +kernel

private theorem truncate_one : NativeFixed.table.Contains #[]
    (#v[1,1,0,47] : Vector (ZMod mersenne31Modulus) 4) := by
  refine ⟨⟨5705986,by decide⟩,?_⟩
  decide +kernel

private theorem fill_one : NativeFixed.table.Contains #[]
    (#v[4,0,0,20] : Vector (ZMod mersenne31Modulus) 4) := by
  refine ⟨⟨393221,by decide⟩,?_⟩
  decide +kernel

private theorem low_member : NativeFixed.table.Contains #[]
    (#v[65537,2,0,37] : Vector (ZMod mersenne31Modulus) 4) := by
  convert at_shift 65537 (by decide) using 1
  decide +kernel

private theorem high_member : NativeFixed.table.Contains #[]
    (#v[65536,0,0,37] : Vector (ZMod mersenne31Modulus) 4) := by
  convert at_shift 65536 (by decide) using 1
  decide +kernel

-- Reindex through a named evaluator so index rewrites never traverse the
-- expanded foreign native matrix. Kernel checks still reduce the exact matrix.
private def polynomialValue (discarded : Bool) (i : Fin 117) : ZMod mersenne31Modulus :=
  ((FlatOperation.constraints (importedConstraints NativeFixed.table)).get i).eval
    (environment (assignment discarded))

private theorem polynomials0 (discarded : Bool) (i : Fin 32) :
    polynomialValue discarded ⟨0 + i.val,by omega⟩ = 0 := by
  cases discarded <;> fin_cases i <;> decide +kernel

private theorem polynomials1 (discarded : Bool) (i : Fin 32) :
    polynomialValue discarded ⟨32 + i.val,by omega⟩ = 0 := by
  cases discarded <;> fin_cases i <;> decide +kernel

private theorem polynomials2 (discarded : Bool) (i : Fin 32) :
    polynomialValue discarded ⟨64 + i.val,by omega⟩ = 0 := by
  cases discarded <;> fin_cases i <;> decide +kernel

private theorem polynomials3 (discarded : Bool) (i : Fin 21) :
    polynomialValue discarded ⟨96 + i.val,by omega⟩ = 0 := by
  cases discarded <;> fin_cases i <;> decide +kernel

private theorem polynomials (discarded : Bool) (i : Fin 117) :
    polynomialValue discarded i = 0 := by
  rcases i with ⟨i,bound⟩
  by_cases h0 : i < 32
  · simpa only [Nat.zero_add] using polynomials0 discarded ⟨i,h0⟩
  by_cases h1 : i < 64
  · have key : 32 + (i - 32) = i := by omega
    simpa only [key] using polynomials1 discarded ⟨i - 32,by omega⟩
  by_cases h2 : i < 96
  · have key : 64 + (i - 64) = i := by omega
    simpa only [key] using polynomials2 discarded ⟨i - 64,by omega⟩
  · have key : 96 + (i - 96) = i := by omega
    simpa only [key] using polynomials3 discarded ⟨i - 96,by omega⟩

private theorem lookups (discarded : Bool) (i : Fin 22) :
    ((FlatOperation.lookups (importedConstraints NativeFixed.table)).get i).Contains
      (environment (assignment discarded)) := by
  cases discarded <;> fin_cases i
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
        ProvableType.fromElements] using truncate_one)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using low_member)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using high_member)
    | (simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Expression.eval,
        environment,assignment,values,Table.toRaw,Table.fromStatic,StaticTable.toTable,
        ProvableType.fromElements] using fill_one)

/-- Every actual117equation and all22lookups are checked against the complete
    actual native fixed pool, including scalar/timestamp and both sign queries. -/
theorem native_constraints (discarded : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment discarded))
      (importedConstraints NativeFixed.table) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · intro expression member
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact polynomials discarded ⟨i.val,i.isLt⟩
  · intro lookup member
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact lookups discarded ⟨i.val,i.isLt⟩

end Tests.NativeReducedWitness
