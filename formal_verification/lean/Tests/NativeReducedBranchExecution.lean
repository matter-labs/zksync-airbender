import Airbender.Proofs.ReducedMachine.NativeBranchExecution

namespace Tests.NativeReducedBranchExecution
open Airbender Arithmetic Trace ReducedMachine Native Verification
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Retained original Sail positives; these are not full native accepted rows.
private def ops : Vector BranchMode 6 := #v[.BEQ,.BNE,.BLT,.BGE,.BLTU,.BGEU]
private def left : Vector (BitVec 32) 3 := #v[1,0x80000000,0x7fffffff]
private def right : Vector (BitVec 32) 3 := #v[1,0x7fffffff,0x80000000]
private def conditions : Vector (Vector Bool 6) 3 :=
  #v[#v[true,false,false,true,false,true],#v[false,true,true,false,false,true],
     #v[false,true,false,true,true,false]]
private def before (sample : Fin 3) (misa : BitVec 32) : State :=
  { (default : State) with regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 left[sample] |>.insert .x2 right[sample] |>.insert .misa misa) }

/-- Independent equal/sign-crossing values cover taken and untaken cases of
    every retained original branch primitive. -/
theorem original_conditions (sample : Fin 3) (op : Fin 6) :
    NativeBranchClauseProofs.nativeCondition ops[op] left[sample] right[sample] = conditions[sample][op] := by
  fin_cases sample <;> fin_cases op <;> decide +kernel

private theorem retire (opcode : BranchMode) (imm : BitVec 13) (state : State)
    (l r pc final : BitVec 32)
    (leftRead : run (SailRV32.Functions.rX_bits (.Regidx 1)) state = .ok l state)
    (rightRead : run (SailRV32.Functions.rX_bits (.Regidx 2)) state = .ok r state)
    (isa : ∃ value, state.regs.get? .misa = some value)
    (calculated : final = if NativeBranchClauseProofs.nativeCondition opcode l r then
      pc+SailRV32.Functions.sign_extend (m := 32) imm else pc+4)
    (aligned : final.toNat % 4 = 0) :
    run (normalStep (SailRV32.Functions.execute_BTYPE imm (.Regidx 2) (.Regidx 1) opcode))
      (retiredState state pc) = .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState state final) := by
  let start := retiredState state pc
  let output : Output := ⟨⟨0,0⟩,Word.ofBitVec final⟩
  have left' := rX_PC (.Regidx 1) (pc := pc) (rX_nextPC (.Regidx 1) (pc := pc) leftRead)
  have right' := rX_PC (.Regidx 2) (pc := pc) (rX_nextPC (.Regidx 2) (pc := pc) rightRead)
  have pcRead := Trace.Proofs.retired_state_pc state pc
  have isa' : ∃ value, start.regs.get? .misa = some value := by
    obtain ⟨value,read⟩ := isa
    exact ⟨value,by simpa [start,retiredState,Std.ExtDHashMap.get?_insert] using read⟩
  have execute := NativeBranchClauseProofs.clause_of_reads opcode imm 1 2 start l r pc final
    left' right' pcRead isa' calculated aligned
  have checked : stepSpec start (SailRV32.Functions.execute_BTYPE imm (.Regidx 2) (.Regidx 1) opcode)
      zeroRegister output := by
    apply retire_of_effects (before := start) (initialPC := pc) (output := output) pcRead
    refine ⟨{ start with regs := start.regs.insert .nextPC final },?_,?_⟩
    · exact execute
    · simp only [writeResult,write_zero,freeM_pure_bind,output,Word.ofBitVec_roundtrip]
      rfl
  obtain ⟨after,normal,projection⟩ := checked
  have write : run (SailRV32.Functions.wX_bits (.Regidx 0) output.destination.toBitVec) start = .ok () start := rfl
  have actual := Trace.Proofs.projected_step_of_write 0 output write
  have same := (EStateM.Result.ok.inj (projection.symm.trans actual)).2
  simpa only [same,start,output,Word.ofBitVec_roundtrip,Trace.Proofs.retired_state_overwrite] using normal

private theorem left_read (sample : Fin 3) (misa : BitVec 32) :
    run (SailRV32.Functions.rX_bits (.Regidx 1)) (before sample misa) = .ok left[sample] (before sample misa) := by
  apply read_register
  simp [before,Std.ExtDHashMap.get?_insert]
private theorem right_read (sample : Fin 3) (misa : BitVec 32) :
    run (SailRV32.Functions.rX_bits (.Regidx 2)) (before sample misa) = .ok right[sample] (before sample misa) := by
  apply read_register
  simp [before,Std.ExtDHashMap.get?_insert]
private theorem isa (sample : Fin 3) (misa : BitVec 32) :
    ∃ value, (before sample misa).regs.get? .misa = some value := by
  exact ⟨misa,by simp [before]⟩

/-- All six original clauses prepare/retire at ordinary and wrapped PCs. The
    supplied initial CSR is arbitrary, including either compressed-ISA bit. -/
theorem original_retirement (sample : Fin 3) (op : Fin 6) (wrap : Bool) (misa : BitVec 32) :
    let pc := if wrap then (0xfffffffc : BitVec 32) else 16
    let final := if conditions[sample][op] then pc+8 else pc+4
    registerClause (.BTYPE (8,.Regidx 2,.Regidx 1,ops[op])) =
      some (SailRV32.Functions.execute_BTYPE 8 (.Regidx 2) (.Regidx 1) ops[op]) ∧
    run (normalStep (SailRV32.Functions.execute_BTYPE 8 (.Regidx 2) (.Regidx 1) ops[op]))
      (retiredState (before sample misa) pc) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (before sample misa) final) := by
  refine ⟨rfl,retire ops[op] 8 _ _ _ _ _ (left_read sample misa) (right_read sample misa) (isa sample misa) ?_ ?_⟩
  · rw [original_conditions]; rfl
  · fin_cases sample <;> fin_cases op <;> cases wrap <;> decide +kernel

/-- Untaken offset bit1 may be set: original BTYPE does not jump or reject it. -/
theorem untaken_halfword_offset (misa : BitVec 32) :
    run (normalStep (SailRV32.Functions.execute_BTYPE 2 (.Regidx 2) (.Regidx 1) .BEQ))
      (retiredState (before 1 misa) 16) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (before 1 misa) 20) := by
  apply retire .BEQ 2 _ _ _ _ _ (left_read 1 misa) (right_read 1 misa) (isa 1 misa) <;> decide +kernel

/-- A taken negative offset wraps the actual RV32 PC and stutters every data component. -/
theorem taken_negative_wrap (misa : BitVec 32) :
    run (normalStep (SailRV32.Functions.execute_BTYPE 8188 (.Regidx 2) (.Regidx 1) .BEQ))
      (retiredState (before 0 misa) 0) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (before 0 misa) 0xfffffffc) := by
  apply retire .BEQ 8188 _ _ _ _ _ (left_read 0 misa) (right_read 0 misa) (isa 0 misa) <;> decide +kernel

end Tests.NativeReducedBranchExecution
