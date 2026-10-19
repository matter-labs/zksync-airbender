import Tests.MulDivRegisters
import Airbender.Review.Trace.Families.MulDiv.Execution

namespace Tests.MulDivExecution
open Airbender Arithmetic Trace MulDiv Reference.RiscV.Sail Reference.Sail
open Tests.MulDivInitializedFixture

/-- All sixteen initialized cases execute the original clauses and actual PC
    preparation/retirement. Both states come from native matching. -/
theorem initialized_execution (op : Operation) (discarded zeroDivisor : Bool) :
    ∃ after : State,
      run (normalStep (clause op 1 2 (if discarded then 0 else 3)))
        (retiredState (before op discarded zeroDivisor) 0) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after 4) ∧
      RegisterTransfer (nativeRow op discarded zeroDivisor) (entry op discarded)
        (before op discarded zeroDivisor) after := by
  obtain ⟨registers,steps⟩ := MulDiv.public_instruction_history (program_image op discarded zeroDivisor)
    (public_inputs op discarded zeroDivisor) (accepted op discarded zeroDivisor)
    (decoded op discarded zeroDivisor) Tests.MulDivRegisters.aligned
  obtain ⟨history,rows,after,_,permutation,_,_,_,_,_,transfers⟩ := registers
  have singleton : rows = [nativeRow op discarded zeroDivisor] :=
    List.perm_singleton.mp (by simpa only [trace] using permutation)
  obtain ⟨actual,present,rowBefore,rowAfter,_,_,_,earlier,current,later,transfer⟩ :=
    transfers [] (nativeRow op discarded zeroDivisor) [] singleton
  have same : actual = entry op discarded := by
    simpa [setup,SparseDecoderSetup.program] using present
  subst actual
  change SailHistory _ [] (before op discarded zeroDivisor) rowBefore at earlier
  change SailHistory _ [] rowAfter after at later
  cases earlier
  cases later
  obtain ⟨actual,present,_,_,execution⟩ := steps (nativeRow op discarded zeroDivisor) (by simp [trace])
  have same : actual = entry op discarded := by
    simpa [setup,SparseDecoderSetup.program] using present
  subst actual
  have checked := execution.2.2 _ _ current
  have start : (Word.mk ((nativeRow op discarded zeroDivisor).assignment 0).val
      ((nativeRow op discarded zeroDivisor).assignment 1).val).toBitVec = 0 := by
    cases op <;> cases discarded <;> cases zeroDivisor <;> rfl
  have finish : (Word.mk ((nativeRow op discarded zeroDivisor).assignment 13).val
      ((nativeRow op discarded zeroDivisor).assignment 14).val).toBitVec = 4 := by
    cases op <;> cases discarded <;> cases zeroDivisor <;> rfl
  rw [start,finish] at checked
  exact ⟨after,by simpa only [entry] using checked,transfer⟩

/-- Discarding the data result still performs the original instruction's PC
    retirement. Its complete post-state follows from the actual masked write. -/
theorem discarded_retirement (op : Operation) (zeroDivisor : Bool) :
    run (normalStep (clause op 1 2 0))
      (retiredState (before op true zeroDivisor) 0) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (before op true zeroDivisor) 4) := by
  obtain ⟨after,checked,transfer⟩ := initialized_execution op true zeroDivisor
  have written := transfer.2
  change run (SailRV32.Functions.wX_bits zeroRegister _)
    (before op true zeroDivisor) = .ok () after at written
  rw [write_zero] at written
  have same := (EStateM.Result.ok.inj written).2
  simpa only [Bool.true_eq,if_true,← same] using checked

end Tests.MulDivExecution
