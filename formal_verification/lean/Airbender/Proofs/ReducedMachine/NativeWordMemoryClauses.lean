import Airbender.Review.Helpers.Memory.ReducedMachineWordMemoryPlatform
import Airbender.Proofs.Sail.VirtualMemory

namespace Airbender.ReducedMachine.NativeWordMemoryClauseProofs
open Native Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Closed native numerical effects recover the exact original RV32 address. -/
theorem address_and_alignment {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (effects : WordMemoryNumericalEffects w entry) :
    (wordMemoryAddressWord w).toBitVec = (sourceWord w).toBitVec+entry.data.immediate.toBitVec ∧
    (wordMemoryAddressWord w).toBitVec.toNat%4 = 0 := by
  have bound : (wordMemoryAddressWord w).Bounded := by rw [effects.address]; exact Word.ofBitVec_bound _
  refine ⟨?_,?_⟩
  · exact (congrArg Word.toBitVec effects.address).trans (Word.ofBitVec_roundtrip _)
  · rw [Word.toBitVec_toNat bound]; exact effects.aligned

/-- Original vmem_read follows the actual source and architectural read. The
    configuration/ordinary inputs are INTERNAL and discharged by public assembly. -/
theorem virtual_load [MemoryPlatform SailRV32.exception]
    {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry} {before after : State}
    (effects : WordMemoryNumericalEffects w entry) (transfer : WordMemoryTransfer w entry before after)
    (load : entry.data.family = false) (configuration : FlatMemoryConfiguration before)
    (ordinary : OrdinaryWordAddress (wordMemoryAddressWord w).toBitVec) :
    run (SailRV32.Functions.vmem_read (.Regidx entry.data.rs1) entry.data.immediate.toBitVec 4
      (.Load .Data) false false false) before = .ok (.Ok (wordMemoryLoadWord w).toBitVec) before := by
  obtain ⟨address,aligned⟩ := address_and_alignment effects
  have read := (transfer.load load).1
  change (readBytes (ue := SailRV32.exception) 4 (wordMemoryAddressWord w).toBitVec.toNat).run before = _ at read
  rw [address] at read aligned ordinary
  exact virtual_word_read configuration _ _ transfer.sourceRead aligned ordinary read

/-- Original vmem_write follows the actual unmasked SW write, retaining its
    OLDREAD and original rs2 read-before-write, including source aliases. -/
theorem virtual_store [MemoryPlatform SailRV32.exception]
    {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry} {before after : State}
    (effects : WordMemoryNumericalEffects w entry) (transfer : WordMemoryTransfer w entry before after)
    (store : entry.data.family = true) (configuration : FlatMemoryConfiguration before)
    (ordinary : OrdinaryWordAddress (wordMemoryAddressWord w).toBitVec) :
    run (SailRV32.Functions.vmem_write (.Regidx entry.data.rs1) entry.data.immediate.toBitVec 4
      (wordMemorySecondWord w).toBitVec (.Store .Data) false false false) before = .ok (.Ok true) after := by
  obtain ⟨address,aligned⟩ := address_and_alignment effects
  have write := (transfer.store store).2
  rw [address] at write aligned ordinary
  exact virtual_memory_write (Or.inr (Or.inr rfl)) configuration _ _ transfer.sourceRead aligned ordinary _ write

/-- Retain original LOAD/STORE clauses and operands. Actual unmasked LW-to-x0
    still reads memory before the original accessor discards its write. No old
    standalone native compiled masks/constraints/tables/acceptance are used. -/
theorem clause [MemoryPlatform SailRV32.exception]
    {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry} {before after : State}
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (effects : WordMemoryNumericalEffects w entry) (transfer : WordMemoryTransfer w entry before after)
    (configuration : FlatMemoryConfiguration before)
    (ordinary : OrdinaryWordAddress (wordMemoryAddressWord w).toBitVec) : WordMemoryClauseEffects entry before after := by
  unfold wordMemoryDecoderFields at fields
  split at fields
  · rename_i imm rs1 rd instruction
    have data : entry.data = ⟨false,rs1,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),1025,2⟩ :=
      (Option.some.inj fields).symm
    have load : entry.data.family = false := by rw [data]
    have read := virtual_load effects transfer load configuration ordinary
    have written := (transfer.load load).2
    rw [data,Word.ofBitVec_roundtrip] at read
    rw [data] at written
    refine ⟨SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4,?_,?_⟩
    · simp [wordMemoryClause,instruction]
    · rw [load_word read,run_bind_of_ok _ _ _ _ _ written]
      rfl
  · rename_i imm rs2 rs1 instruction
    have data : entry.data = ⟨true,rs1,rs2,0,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),16386,2⟩ :=
      (Option.some.inj fields).symm
    have store : entry.data.family = true := by rw [data]
    have read := (transfer.store store).1
    have write := virtual_store effects transfer store configuration ordinary
    rw [data] at read
    rw [data,Word.ofBitVec_roundtrip] at write
    exact ⟨SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4,
      by simp [wordMemoryClause,instruction],store_word read write⟩
  · cases fields

end Airbender.ReducedMachine.NativeWordMemoryClauseProofs
