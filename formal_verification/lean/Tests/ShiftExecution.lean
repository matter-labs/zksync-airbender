import Tests.ShiftRegisters
import Airbender.Review.Trace.Families.ShiftBinop.Execution

namespace Tests.ShiftExecution
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Airbender Arithmetic Trace ShiftBinop Reference.RiscV.Sail Reference.Sail
open Tests.ShiftHistoryFixture

/-- All twenty-four complete native rows construct actual original Sail retired
    executions from original public code/seeds/PC and accepted native matching.
    The after-state also carries the actual native transfer and code/misa frames. -/
theorem initialized_execution (sample : Fin 24) :
    ∃ after : State, ∃ clause,
      registerClause NativeSetup.entries[sample.val].instruction = some clause ∧
      run (normalStep clause) (retiredState (ShiftValuesFixture.before sample)
          (BitVec.ofNat 32 (4 * sample.val))) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (BitVec.ofNat 32 (4 * sample.val + 4))) ∧
      RegisterTransfer (nativeRow sample) NativeSetup.entries[sample.val]
        (ShiftValuesFixture.before sample) after ∧
      after.mem = (ShiftValuesFixture.before sample).mem ∧
      after.regs.get? .misa = (ShiftValuesFixture.before sample).regs.get? .misa := by
  obtain ⟨registers,clauses⟩ := ShiftBinop.public_instruction_history
    (ShiftValuesFixture.program_image sample) (ShiftValuesFixture.public_inputs sample)
    (accepted sample) (ShiftValuesFixture.decoded sample) ShiftRegisters.aligned
  obtain ⟨history,rows,after,_,permutation,_,_,_,memory,isa,transfers⟩ := registers
  have singleton : rows = [nativeRow sample] :=
    List.perm_singleton.mp (by simpa only [trace] using permutation)
  obtain ⟨entry,present,rowBefore,rowAfter,_,_,query,earlier,current,later,transfer⟩ :=
    transfers [] (nativeRow sample) [] singleton
  have same := ShiftRegisters.entry_unique sample present query
  subst entry
  change SailHistory _ [] (ShiftValuesFixture.before sample) rowBefore at earlier
  change SailHistory _ [] rowAfter after at later
  cases earlier
  cases later
  obtain ⟨entry,present,_,query,execute⟩ := clauses (nativeRow sample) (by simp [trace])
  have same := ShiftRegisters.entry_unique sample present query
  subst entry
  obtain ⟨clause,dispatch,execution⟩ := execute.2 _ _ current
  have start : (Word.mk ((nativeRow sample).assignment 0).val
      ((nativeRow sample).assignment 1).val).toBitVec = BitVec.ofNat 32 (4 * sample.val) := by
    fin_cases sample <;> rfl
  have finish : (Word.mk ((nativeRow sample).assignment 13).val
      ((nativeRow sample).assignment 14).val).toBitVec = BitVec.ofNat 32 (4 * sample.val + 4) := by
    fin_cases sample <;> rfl
  rw [start,finish] at execution
  exact ⟨after,clause,dispatch,execution,transfer,memory,isa⟩

/-- The original x0 instructions actually execute and preserve data
    while advancing PC, including all six immediate forms and aliases. -/
theorem discarded_retirement (i : Fin 12) :
    ∃ clause, registerClause NativeSetup.entries[12 + i.val].instruction = some clause ∧
      run (normalStep clause)
        (retiredState (ShiftValuesFixture.before ⟨12 + i.val,by omega⟩)
          (BitVec.ofNat 32 (4 * (12 + i.val)))) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState (ShiftValuesFixture.before ⟨12 + i.val,by omega⟩)
            (BitVec.ofNat 32 (4 * (12 + i.val) + 4))) := by
  let sample : Fin 24 := ⟨12 + i.val,by omega⟩
  obtain ⟨after,clause,dispatch,execution,transfer,_,_⟩ := initialized_execution sample
  have zero : NativeSetup.entries[sample.val].data.rd = 0 := by fin_cases i <;> rfl
  have written := transfer.2
  change run (SailRV32.Functions.wX_bits (.Regidx NativeSetup.entries[sample.val].data.rd) _)
    (ShiftValuesFixture.before sample) = .ok () after at written
  rw [zero] at written
  have pureWrite : run (SailRV32.Functions.wX_bits (.Regidx 0)
      (memoryWord (importedConstraintsMemoryPorts[2].writeCode (nativeRow sample).assignment)))
      (ShiftValuesFixture.before sample) = .ok () (ShiftValuesFixture.before sample) := rfl
  have same := (EStateM.Result.ok.inj (written.symm.trans pureWrite)).2
  exact ⟨clause,dispatch,by simpa only [same] using execution⟩

end Tests.ShiftExecution
