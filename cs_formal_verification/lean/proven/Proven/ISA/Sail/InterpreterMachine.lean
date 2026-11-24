import Proven.ISA.Sail.Interpreter

/-! The Airbender machine with lean-sail's interpreter: a delegation call gives close results on the state that the
    lean-sail state describes, and a Sail instruction runs the same under both interpreters. -/

open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human

namespace Proven.Interpreter
open Airbender Airbender.Reference.RiscV.Sail.Configuration

/-- Every 32-bit address is below `requestReach`. -/
theorem word_reach (address : BitVec 32) : address.toNat < requestReach := by
  have bound := address.isLt
  unfold requestReach maxRequestBytes
  omega

/-- The state that an agreeing lean-sail state describes is close to the `SailState`. -/
theorem view_close {state : SailState} {sequential : SequentialSailState}
    (agrees : SequentialAgrees state sequential) : Close state sequential.view := by
  refine ⟨?_, ?_, agrees.cycles.symm⟩
  · funext register
    change _ = (sequential.regs.get? register).getD _
    rw [agrees.regs register]
    rfl
  · intro address reach
    change _ = (sequential.mem.get? address).getD 0
    rw [agrees.mem address reach]
    rfl

/-- Updating an agreeing lean-sail state with a close state keeps the agreement. -/
theorem update_agrees {state state' other : SailState} {sequential : SequentialSailState}
    (agrees : SequentialAgrees state sequential) (close : Close state' other) :
    SequentialAgrees state' (sequential.update other) := by
  refine ⟨?_, ?_, close.cycles.symm⟩
  · intro register
    change (sequential.regs.map fun register _ => other.regs register).get? register = _
    rw [Std.ExtDHashMap.get?_map, agrees.regs register, close.regs]
    rfl
  · intro address reach
    have present := agrees.mem address reach
    rw [Std.ExtHashMap.get?_eq_getElem?] at present
    change (sequential.mem.map fun address _ => other.mem address).get? address = _
    rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_map, present, close.mem address reach]
    rfl

/-- Register reads give the same value on close states. -/
theorem getReg_close {state other : SailState} (close : Close state other) (index : RV.Reg) :
    getReg state index = getReg other index := by
  have reads := runSail_close (rX_bits (.Regidx index)) state other close
  unfold getReg
  revert reads
  cases runSail (rX_bits (.Regidx index)) state <;> cases runSail (rX_bits (.Regidx index)) other
  · intro reads; exact reads.1
  · intro reads; exact reads.elim
  · intro reads; exact reads.elim
  · intro _; rfl

/-- Delegation RAM is the same on close states. -/
theorem ramView_close {state other : SailState} (close : Close state other) (shadow : Shadow) :
    ramView state shadow = ramView other shadow := by
  funext address
  unfold ramView
  by_cases below : address.toNat < RV.ROM_END
  · rw [ite_eq_left below, ite_eq_left below]
  · rw [ite_eq_right below, ite_eq_right below]
    exact close.mem address.toNat (word_reach address)

/-- The state after a register write program is close on close states. -/
theorem written_close {state other : SailState} (close : Close state other) (program : SailM Unit) :
    Close (match runSail program state with | .ok _ state' => state' | .error _ state' => state')
      (match runSail program other with | .ok _ other' => other' | .error _ other' => other') := by
  have result := runSail_close program state other close
  revert result
  cases runSail program state <;> cases runSail program other
  · intro result; exact result.2
  · intro result; exact result.elim
  · intro result; exact result.elim
  · intro result; exact result.2

/-- A delegation effect gives close states with the same shadow RAM. -/
theorem applyEffect_close {state other : SailState} (close : Close state other) (shadow : Shadow)
    (effect : RV.Effect) :
    Option.Rel (fun first second => Close first.1 second.1 ∧ first.2 = second.2)
      (Airbender.applyEffect state shadow effect) (Airbender.applyEffect other shadow effect) := by
  have pc : state.regs .PC = other.regs .PC := congrFun close.regs .PC
  unfold Airbender.applyEffect
  rw [ramView_close close shadow, pc]
  by_cases aligned : (effect.writes.all fun write => decide (RV.aligned write.1 4)) = true
  · rw [ite_eq_left aligned, ite_eq_left aligned]
    refine .some ⟨?_, rfl⟩
    apply set_close
    apply set_close
    apply written_close
    refine ⟨close.regs, ?_, close.cycles⟩
    intro address reach
    by_cases inside : RV.ROM_END ≤ address ∧ address < 2 ^ 32
    · simp only [inside, and_self, ite_true]
    · simp only [inside, ite_false]
      exact close.mem address reach
  · rw [ite_eq_right aligned, ite_eq_right aligned]
    exact .none

/-- A delegation call gives close results on close states. -/
theorem delegation_close {state other : SailState} (close : Close state other) (shadow : Shadow) :
    Option.Rel (Option.Rel fun first second => Close first.1 second.1 ∧ first.2 = second.2)
      (delegation state shadow) (delegation other shadow) := by
  have memory : (fun address : RV.Word => state.mem address.toNat) = fun address => other.mem address.toNat := by
    funext address
    exact close.mem address.toNat (word_reach address)
  have pc : state.regs .PC = other.regs .PC := congrFun close.regs .PC
  have related := applyEffect_close close shadow
  unfold delegation
  dsimp only
  rw [pc, memory, getReg_close close 10, getReg_close close 11, getReg_close close 12, ramView_close close shadow]
  generalize Airbender.applyEffect state shadow = first at related ⊢
  generalize Airbender.applyEffect other shadow = second at related ⊢
  split
  · split
    · rename_i kind _
      refine .some ?_
      cases RV.Delegation.effect kind _ _ _ _ with
      | none => exact .none
      | some effect => exact related effect
    · exact .none
  · exact .none

/-- One machine step is one step with lean-sail's interpreter from every agreeing lean-sail state. -/
theorem step_sequential {machine machine' : Machine} {sequential : SequentialSailState}
    (agrees : SequentialAgrees machine.sail sequential) (stepped : step machine = some machine') :
    ∃ sequential', SequentialMachine.step ⟨sequential, machine.shadow, machine.input⟩ =
        some ⟨sequential', machine'.shadow, machine'.input⟩ ∧ SequentialAgrees machine'.sail sequential' := by
  obtain ⟨state, shadow, inputs⟩ := machine
  have related := delegation_close (view_close agrees) shadow
  unfold step at stepped
  unfold SequentialMachine.step
  dsimp only at stepped ⊢
  generalize delegation state shadow = ours at related stepped
  generalize delegation sequential.view shadow = theirs at related ⊢
  cases related with
  | none =>
    dsimp only at stepped ⊢
    cases run : runSail (sailStep (inputs.headD 0)) state with
    | error error state' =>
      rw [run] at stepped
      cases stepped
    | ok result state' =>
      rw [run] at stepped
      obtain ⟨sequential', sequentialRun, agrees'⟩ := transport _ _ _ _ _ agrees run
      rw [sequentialRun]
      rcases result with _ | _ | _ <;> cases inputs <;> cases stepped <;> exact ⟨sequential', rfl, agrees'⟩
  | some inner =>
    cases inner with
    | none => cases stepped
    | some pair =>
      rename_i first second
      obtain ⟨state', shadow'⟩ := first
      obtain ⟨other', otherShadow⟩ := second
      obtain ⟨close', same⟩ := pair
      cases stepped
      cases same
      exact ⟨_, rfl, update_agrees agrees close'⟩

/-- Every finite machine run is a run of the same length with lean-sail's interpreter. -/
theorem machine_run_is_sequential : MachineRunIsSequentialClaim := by
  intro n
  induction n with
  | zero =>
    intro machine machine' sequential agrees run
    cases run
    exact ⟨sequential, rfl, agrees⟩
  | succ n ih =>
    intro machine machine' sequential agrees run
    change (step machine).bind (Machine.run n) = some machine' at run
    cases stepped : step machine with
    | none => rw [stepped] at run; cases run
    | some middle =>
      rw [stepped] at run
      obtain ⟨sequentialMiddle, sequentialStep, agreesMiddle⟩ := step_sequential agrees stepped
      obtain ⟨sequential', sequentialRun, agrees'⟩ := ih middle machine' sequentialMiddle agreesMiddle run
      refine ⟨sequential', ?_, agrees'⟩
      change (SequentialMachine.step _).bind (SequentialMachine.run n) = _
      rw [sequentialStep]
      exact sequentialRun

end Proven.Interpreter
