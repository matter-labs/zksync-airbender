import Tests.ShiftResults
import Airbender.Review.Trace.Families.ShiftBinop.Registers

namespace Tests.ShiftRegisters
open Airbender Arithmetic Trace ShiftBinop Reference.RiscV.Sail Reference.Sail
open Tests.ShiftHistoryFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem aligned : ∀ cell ∈ [Cell.register 0,.register 1,.register 2,.register 3], cell.Aligned := by
  intro cell member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [Cell.Aligned]

theorem entry_query_pc (sample : Fin 24) :
    ((NativeSetup.entries[sample.val].query (p := mersenne31Modulus))[0]).val = 4 * sample.val := by
  fin_cases sample <;> rfl

/-- The actual native public PC query identifies the original fixture entry. -/
theorem entry_unique (sample : Fin 24) {entry : ShiftBinop.ProgramEntry}
    (present : entry ∈ NativeSetup.setup.program)
    (query : (nativeRow sample).decoderQuery = entry.query) :
    entry = NativeSetup.entries[sample.val] := by
  change entry ∈ NativeSetup.entries.toList at present
  obtain ⟨index,same⟩ := List.mem_iff_get.mp present
  let i : Fin 24 := ⟨index.val,by simpa using index.isLt⟩
  have found : NativeSetup.entries[i.val] = entry := by simpa [i] using same
  rw [← found] at query ⊢
  have low := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => (q[0]).val) query
  have native : ((nativeRow sample).decoderQuery[0]).val = 4 * sample.val := by
    fin_cases sample <;> rfl
  rw [native,entry_query_pc] at low
  have equal : i = sample := Fin.ext (by omega)
  rw [equal]

/-- All twenty-four accepted initialized rows construct actual Sail segment
    states and original GPR transfers from public bytes and native matching. -/
theorem initialized_transfers (sample : Fin 24) :
    ∃ after : State, RegisterTransfer (nativeRow sample) NativeSetup.entries[sample.val]
        (ShiftValuesFixture.before sample) after ∧
      NativeSetup.entries[sample.val].SourceWith (ShiftValuesFixture.before sample)
        ShiftBinop.decoderFields ∧
      after.mem = (ShiftValuesFixture.before sample).mem ∧
      after.regs.get? .misa = (ShiftValuesFixture.before sample).regs.get? .misa := by
  obtain ⟨history,rows,after,_,permutation,_,_,_,memory,isa,transfers⟩ :=
    ShiftBinop.public_register_history (ShiftValuesFixture.program_image sample)
      (ShiftValuesFixture.public_inputs sample) (accepted sample)
      (ShiftValuesFixture.decoded sample) aligned
  have singleton : rows = [nativeRow sample] :=
    List.perm_singleton.mp (by simpa only [trace] using permutation)
  obtain ⟨entry,present,rowBefore,rowAfter,source,_,query,earlier,_,later,transfer⟩ :=
    transfers [] (nativeRow sample) [] singleton
  have same := entry_unique sample present query
  subst entry
  change SailHistory _ [] (ShiftValuesFixture.before sample) rowBefore at earlier
  change SailHistory _ [] rowAfter after at later
  cases earlier
  cases later
  exact ⟨after,transfer,source,memory,isa⟩

/-- The actual native masked destination is written by original Sail, with
    every source and old-destination read retained in the same real pre-state. -/
theorem actual_write (sample : Fin 24) :
    ∃ after : State, run (SailRV32.Functions.wX_bits
        (.Regidx NativeSetup.entries[sample.val].data.rd)
        (writtenWord (ShiftHistoryRows.assignment sample)).toBitVec)
        (ShiftValuesFixture.before sample) = .ok () after ∧
      after.mem = (ShiftValuesFixture.before sample).mem ∧
      after.regs.get? .misa = (ShiftValuesFixture.before sample).regs.get? .misa := by
  obtain ⟨after,transfer,_,memory,isa⟩ := initialized_transfers sample
  refine ⟨after,?_,memory,isa⟩
  simpa [RegisterTransfer,importedConstraintsMemoryPorts,MemoryPort.writeCode,
    WordColumns.code,WordColumns.evaluate,pairCode,memoryWord,Nat.unpair_pair,
    writtenWord,nativeRow] using transfer.2

/-- Numerical results now feed an actual original Sail write, including exact
    native x0 masking, without a supplied intermediate or expected after-state. -/
theorem result_write (sample : Fin 24) :
    ∃ after : State, run (SailRV32.Functions.wX_bits
        (.Regidx NativeSetup.entries[sample.val].data.rd)
        (if NativeSetup.entries[sample.val].data.rd = 0 then 0 else
          NativeSetup.entries[sample.val].data.family.result
            (left (ShiftHistoryRows.assignment sample)) (right (ShiftHistoryRows.assignment sample))))
        (ShiftValuesFixture.before sample) = .ok () after ∧
      after.mem = (ShiftValuesFixture.before sample).mem ∧
      after.regs.get? .misa = (ShiftValuesFixture.before sample).regs.get? .misa := by
  obtain ⟨after,write,memory,isa⟩ := actual_write sample
  refine ⟨after,?_,memory,isa⟩
  rw [(ShiftResults.concrete_results sample).2] at write
  by_cases zero : NativeSetup.entries[sample.val].data.rd = 0
  · simp only [if_pos zero] at write ⊢
    exact write
  · simpa only [if_neg zero,Word.ofBitVec_roundtrip] using write

/-- All twelve original x0 variants preserve the whole Sail data state, even
    when immediate rs2 and destination alias and the selected result is nonzero. -/
theorem discarded_state (i : Fin 12) :
    ∃ after : State, RegisterTransfer (nativeRow ⟨12 + i.val,by omega⟩)
      NativeSetup.entries[12 + i.val] (ShiftValuesFixture.before ⟨12 + i.val,by omega⟩) after ∧
      after = ShiftValuesFixture.before ⟨12 + i.val,by omega⟩ := by
  let sample : Fin 24 := ⟨12 + i.val,by omega⟩
  obtain ⟨after,transfer,_,_,_⟩ := initialized_transfers sample
  have zero : NativeSetup.entries[sample.val].data.rd = 0 := by fin_cases i <;> rfl
  have written := transfer.2
  change run (SailRV32.Functions.wX_bits (.Regidx NativeSetup.entries[sample.val].data.rd) _)
    (ShiftValuesFixture.before sample) = .ok () after at written
  rw [zero] at written
  have pureWrite : run (SailRV32.Functions.wX_bits (.Regidx 0)
      (memoryWord (importedConstraintsMemoryPorts[2].writeCode (nativeRow sample).assignment)))
      (ShiftValuesFixture.before sample) = .ok () (ShiftValuesFixture.before sample) := rfl
  exact ⟨after,transfer,(EStateM.Result.ok.inj (written.symm.trans pureWrite)).2⟩

end Tests.ShiftRegisters
