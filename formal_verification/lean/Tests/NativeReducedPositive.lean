import Tests.NativeReducedFixture

namespace Tests.NativeReducedPositive
open Airbender Arithmetic Trace ReducedMachine Native
open Reference.RiscV.Sail Reference.Sail
open Tests.NativeReducedFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Two complete nonempty actual-native fixtures satisfy every public interface
    and execute original fetched SLL, ordinary and x0, to actual native endpoints. -/
theorem initialized_execution (discarded : Bool) :
    (trace discarded).terminal.word.Bounded ∧
    Realizes (StepWith shiftDecoderFields registerClause setup.program)
      (fixedData (trace discarded)) (before discarded)
      [.register 0,.register 1,.register 2,.register 3] :=
  public_shift_execution (program_image discarded) (public_inputs discarded)
    (accepted discarded) (decoded discarded) (by intro cell member; simp at member; rcases member with rfl | rfl | rfl | rfl <;> trivial)

/-- Original Sail PC and GPR reads are consequences of initialized accepted
    native execution. No final state, result, bound or read is assumed. -/
theorem initialized_values (discarded : Bool) : ∃ after : State,
    Relation.ReflTransGen (StepWith shiftDecoderFields registerClause setup.program)
      (before discarded) after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok (publicPC discarded + 4) after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 3)) after =
      .ok (if discarded then (0 : BitVec 32) else 2) after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 0)) after = .ok (0 : BitVec 32) after := by
  obtain ⟨after,steps,pc,reads⟩ := (initialized_execution discarded).2
  let sink := (trace discarded).terminalMemory[3]'(by simp [trace])
  have member : sink ∈ (fixedData (trace discarded)).terminalMemory := List.getElem_mem (by simp [fixedData,trace])
  obtain ⟨cell,present,address,read⟩ := reads sink member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · have impossible : (Cell.register 0).addressCode ≠ sink.address := by cases discarded <;> decide +kernel
    exact False.elim (impossible address)
  · have impossible : (Cell.register 1).addressCode ≠ sink.address := by cases discarded <;> decide +kernel
    exact False.elim (impossible address)
  · have impossible : (Cell.register 2).addressCode ≠ sink.address := by cases discarded <;> decide +kernel
    exact False.elim (impossible address)
  · have word : (id sink).word.toBitVec = if discarded then (0 : BitVec 32) else 2 := by
      cases discarded <;> decide +kernel
    have endpoint : (fixedData (trace discarded)).terminal.word.toBitVec = publicPC discarded + 4 := by
      cases discarded <;> decide +kernel
    rw [word] at read
    rw [endpoint] at pc
    exact ⟨after,steps,pc,read,rfl⟩

/-- The discarded native row retains the same nonzero source/amount/candidate,
    while only the actual destination write is masked to zero. -/
theorem candidate_participation (discarded : Bool) :
    (sourceWord (NativeReducedWitness.assignment discarded)).toBitVec = 1 ∧
    (operandWord (NativeReducedWitness.assignment discarded)).toBitVec = 1 ∧
    (candidateWord (NativeReducedWitness.assignment discarded)).toBitVec = 2 ∧
    (writtenWord (NativeReducedWitness.assignment discarded)).toBitVec =
      if discarded then (0 : BitVec 32) else 2 := by
  cases discarded <;> decide +kernel

private theorem actual_write_equation {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints fixed)) : w 17 * w 118 - w 17 * w 43 = 0 := by
  have equation := Verification.assertion_of_holds holds ⟨106,by change 106 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,Verification.environment] at equation
  linear_combination equation

/-- Changing the actual masked port write rejects full native constraints, in
    both complete fixtures. This is a checked rejection, not a native defect. -/
theorem corrupted_actual_write_rejected (discarded : Bool) :
    ¬ FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun i => if i = 43 then NativeReducedWitness.assignment discarded i + 1
        else NativeReducedWitness.assignment discarded i)) (importedConstraints NativeFixed.table) := by
  intro forged
  have bad := actual_write_equation forged
  cases discarded <;> norm_num [NativeReducedWitness.assignment,NativeReducedWitness.values] at bad

end Tests.NativeReducedPositive
