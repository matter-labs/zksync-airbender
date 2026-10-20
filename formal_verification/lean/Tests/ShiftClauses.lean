import Tests.ShiftRegisters
import Airbender.Review.Trace.Families.ShiftBinop.Clauses

namespace Tests.ShiftClauses
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Airbender Arithmetic Trace ShiftBinop Reference.RiscV.Sail Reference.Sail
open Tests.ShiftHistoryFixture

/-- All twenty-four complete native rows construct actual original Sail clause
    executions from original public code/seeds/PC and accepted native matching.
    The after-state also carries the actual native transfer and code/misa frames. -/
theorem initialized_clauses (sample : Fin 24) :
    ∃ after : State, ∃ clause,
      registerClause NativeSetup.entries[sample.val].instruction = some clause ∧
      run clause (ShiftValuesFixture.before sample) =
        .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
      RegisterTransfer (nativeRow sample) NativeSetup.entries[sample.val]
        (ShiftValuesFixture.before sample) after ∧
      after.mem = (ShiftValuesFixture.before sample).mem ∧
      after.regs.get? .misa = (ShiftValuesFixture.before sample).regs.get? .misa := by
  obtain ⟨registers,clauses⟩ := ShiftBinop.public_clause_history
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
  obtain ⟨clause,dispatch,execution⟩ := execute _ _ current
  exact ⟨after,clause,dispatch,execution,transfer,memory,isa⟩

/-- The original x0 instructions actually execute and preserve the whole data
    state, including all six immediate forms with readonly/destination aliases. -/
theorem discarded_clauses (i : Fin 12) :
    ∃ clause, registerClause NativeSetup.entries[12 + i.val].instruction = some clause ∧
      run clause (ShiftValuesFixture.before ⟨12 + i.val,by omega⟩) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (ShiftValuesFixture.before ⟨12 + i.val,by omega⟩) := by
  let sample : Fin 24 := ⟨12 + i.val,by omega⟩
  obtain ⟨after,clause,dispatch,execution,transfer,_,_⟩ := initialized_clauses sample
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

/-- RV64-sized immediate amounts remain excluded by actual original decoding
    into this RV32 native profile; the clause proof does not widen the profile. -/
theorem illegal_shift_immediates :
    ∀ operation ∈ [SailRV32.sop.SLLI,.SRLI,.SRAI],
      ShiftBinop.decoderFields (.SHIFTIOP (32,.Regidx 1,.Regidx 3,operation)) = none ∧
      ShiftBinop.decoderFields (.SHIFTIOP (63,.Regidx 1,.Regidx 0,operation)) = none := by
  decide +kernel

end Tests.ShiftClauses
