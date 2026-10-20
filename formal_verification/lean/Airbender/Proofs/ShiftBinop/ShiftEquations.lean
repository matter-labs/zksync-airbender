import Airbender.Proofs.ShiftBinop.ShiftParts
import Airbender.Proofs.ShiftBinop.Routing

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

structure ShiftEquations (w : Nat → ZMod mersenne31Modulus) (kind : ShiftKind) : Prop where
  truncation : w 39 = w 27 ∧ w 40 = w 29 ∧ w 41 = w 30
  keys : ∀ slot : Fin 3, w (43 + 4 * slot.val) =
    if kind.parts[slot.val] = .zero then 0 else w (kind.sourceColumn slot) + 65536 * w 29
  low : w 44 + w 48 + w 52 = w 55
  high : w 45 + w 49 + w 53 = w 56

/-- Native operation equations retain actual packed input keys and selected sums. -/
theorem shift_equations {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (kind : ShiftKind) (immediate : Bool)
    (mask : w 12 = ((kind.operation.mask + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus)) :
    ShiftEquations w kind := by
  obtain ⟨sll,srl,sra,binary,csr,_⟩ := selected_bits holds kind.operation immediate mask
  have e21 := assertion_of_holds holds ⟨21, by rw [constraint_count]; decide⟩
  have e22 := assertion_of_holds holds ⟨22, by rw [constraint_count]; decide⟩
  have e23 := assertion_of_holds holds ⟨23, by rw [constraint_count]; decide⟩
  have e25 := assertion_of_holds holds ⟨25, by rw [constraint_count]; decide⟩
  have e26 := assertion_of_holds holds ⟨26, by rw [constraint_count]; decide⟩
  have e27 := assertion_of_holds holds ⟨27, by rw [constraint_count]; decide⟩
  have e29 := assertion_of_holds holds ⟨29, by rw [constraint_count]; decide⟩
  have e30 := assertion_of_holds holds ⟨30, by rw [constraint_count]; decide⟩
  have e31 := assertion_of_holds holds ⟨31, by rw [constraint_count]; decide⟩
  have e33 := assertion_of_holds holds ⟨33, by rw [constraint_count]; decide⟩
  have e34 := assertion_of_holds holds ⟨34, by rw [constraint_count]; decide⟩
  have e35 := assertion_of_holds holds ⟨35, by rw [constraint_count]; decide⟩
  have e37 := assertion_of_holds holds ⟨37, by rw [constraint_count]; decide⟩
  have e38 := assertion_of_holds holds ⟨38, by rw [constraint_count]; decide⟩
  cases kind <;> cases immediate
  all_goals
    simp only [ShiftKind.operation,Operation.isBinary,reduceCtorEq,if_true,if_false] at sll srl sra binary
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
      sll,srl,sra,binary,csr] at e21 e22 e23 e25 e26 e27 e29 e30 e31 e33 e34 e35 e37 e38
    refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
    · linear_combination -e21
    · linear_combination -e22
    · linear_combination -e23
    · intro slot
      fin_cases slot <;> simp [ShiftKind.parts,ShiftKind.sourceColumn]
      all_goals first | linear_combination -e25 | linear_combination -e29 | exact e33 | linear_combination -e33
    · first | (rw [e34]; linear_combination e37 - e26 - e30) | linear_combination e37 - e26 - e30 - e34
    · first | (rw [e35]; linear_combination e38 - e27 - e31) | linear_combination e38 - e27 - e31 - e35

/-- All three actual contribution slots resolve through their derived native tags. -/
theorem shift_part_members {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (kind : ShiftKind) (immediate : Bool)
    (mask : w 12 = ((kind.operation.mask + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.operation.funct3 : ZMod mersenne31Modulus)) (slot : Fin 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[]
      ((partQuery w slot).push ((kind.parts[slot.val]).tag : ZMod mersenne31Modulus)) := by
  have routing := selected_routing holds kind.operation immediate mask tag
  have t1 := routing.1 ⟨1,by decide⟩
  have t2 := routing.1 ⟨2,by decide⟩
  have t3 := routing.1 ⟨3,by decide⟩
  cases kind <;> fin_cases slot
  all_goals
    norm_num [ShiftKind.operation,Operation.lookupTags] at t1 t2 t3
    dsimp [partQuery,ShiftKind.parts,ShiftPart.tag]
    change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[_,_,_,_]
    first
    | simpa [t1] using native_lookup_queries holds ⟨1,by decide⟩
    | simpa [t2] using native_lookup_queries holds ⟨2,by decide⟩
    | simpa [t3] using native_lookup_queries holds ⟨3,by decide⟩

/-- Native truncation forces a bounded low operand, its RV32 low-five-bit amount
    and the actual zero padding field; no input-range premise is supplied. -/
theorem shift_truncation {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (kind : ShiftKind) (immediate : Bool)
    (mask : w 12 = ((kind.operation.mask + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.operation.funct3 : ZMod mersenne31Modulus)) :
    (w 27).val < 65536 ∧ (w 29).val = (w 27).val % 32 ∧ w 30 = 0 := by
  have equations := shift_equations holds kind immediate mask
  have routing := selected_routing holds kind.operation immediate mask tag
  have firstTag : w 42 = 47 := by
    have chosen := routing.1 ⟨0,by decide⟩
    cases kind <;> exact chosen
  have accepted := native_lookup_queries holds ⟨0,by decide⟩
  have native : (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[]
      ((#v[w 27,w 29,w 30]).push (47 : ZMod mersenne31Modulus)) := by
    change (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[w 27,w 29,w 30,47]
    simpa only [equations.truncation.1,equations.truncation.2.1,equations.truncation.2.2,firstTag] using accepted
  exact native_shift_truncation _ ((native_lookup_scalar .truncate _).mp native)

end Airbender.ShiftBinop.Proofs
