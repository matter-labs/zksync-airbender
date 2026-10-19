import Tests.MulDivInitializedFixture
import Airbender.Review.Trace.Families.MulDiv.Registers

namespace Tests.MulDivRegisters
open Airbender Arithmetic Trace MulDiv Reference.RiscV.Sail Reference.Sail
open Tests.MulDivInitializedFixture

theorem aligned : ∀ cell ∈ [Cell.register 0,.register 1,.register 2,.register 3], cell.Aligned := by
  intro cell member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [Cell.Aligned]

/-- Sixteen nonempty initialized traces reach actual Sail register transfers;
    the entry and both segment states come from public bytes/native matching. -/
theorem initialized_transfers (op : Operation) (discarded zeroDivisor : Bool) :
    ∃ after : State, RegisterTransfer (nativeRow op discarded zeroDivisor) (entry op discarded)
        (before op discarded zeroDivisor) after ∧
      (entry op discarded).SourceWith (before op discarded zeroDivisor) MulDiv.decoderFields ∧
      after.mem = (before op discarded zeroDivisor).mem ∧
      after.regs.get? .misa = (before op discarded zeroDivisor).regs.get? .misa := by
  obtain ⟨history,rows,after,_,permutation,_,_,_,memory,isa,transfers⟩ :=
    MulDiv.public_register_history (program_image op discarded zeroDivisor)
      (public_inputs op discarded zeroDivisor) (accepted op discarded zeroDivisor)
      (decoded op discarded zeroDivisor) aligned
  have singleton : rows = [nativeRow op discarded zeroDivisor] :=
    List.perm_singleton.mp (by simpa only [trace] using permutation)
  obtain ⟨actual,present,rowBefore,rowAfter,_,source,_,earlier,_,later,transfer⟩ :=
    transfers [] (nativeRow op discarded zeroDivisor) [] singleton
  have same : actual = entry op discarded := by
    simpa [setup,SparseDecoderSetup.program] using present
  subst actual
  change SailHistory _ [] (before op discarded zeroDivisor) rowBefore at earlier
  change SailHistory _ [] rowAfter after at later
  cases earlier
  cases later
  exact ⟨after,transfer,source,memory,isa⟩

/-- The actual masked native destination word is written by original Sail;
    the write is derived, without supplying a state or expected-result premise. -/
theorem actual_write (op : Operation) (discarded zeroDivisor : Bool) :
    ∃ after : State, run (SailRV32.Functions.wX_bits
        (.Regidx (if discarded then 0 else 3))
        (writtenWord (assignment op discarded zeroDivisor)).toBitVec)
        (before op discarded zeroDivisor) = .ok () after ∧
      after.mem = (before op discarded zeroDivisor).mem ∧
      after.regs.get? .misa = (before op discarded zeroDivisor).regs.get? .misa := by
  obtain ⟨after,transfer,_,memory,isa⟩ := initialized_transfers op discarded zeroDivisor
  refine ⟨after,?_,memory,isa⟩
  simpa [RegisterTransfer,entry,importedConstraintsMemoryPorts,MemoryPort.writeCode,
    WordColumns.code,WordColumns.evaluate,pairCode,memoryWord,Nat.unpair_pair,writtenWord,nativeRow]
    using transfer.2

/-- Original x0 writes preserve the entire Sail state, even for nonzero results. -/
theorem discarded_state (op : Operation) (zeroDivisor : Bool) :
    ∃ after : State, RegisterTransfer (nativeRow op true zeroDivisor) (entry op true)
      (before op true zeroDivisor) after ∧ after = before op true zeroDivisor := by
  obtain ⟨after,transfer,_,_,_⟩ := initialized_transfers op true zeroDivisor
  have written := transfer.2
  change run (SailRV32.Functions.wX_bits (.Regidx 0) _) (before op true zeroDivisor) = .ok () after at written
  have pureWrite : run (SailRV32.Functions.wX_bits (.Regidx 0)
      (memoryWord (importedConstraintsMemoryPorts[2].writeCode
        (nativeRow op true zeroDivisor).assignment))) (before op true zeroDivisor) =
      .ok () (before op true zeroDivisor) := rfl
  exact ⟨after,transfer,(EStateM.Result.ok.inj (written.symm.trans pureWrite)).2⟩

end Tests.MulDivRegisters
