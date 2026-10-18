import Tests.ControlValues
import Airbender.Review.Trace.Families.JumpBranchSlt.Registers

namespace Tests.ControlRegisters
open Airbender Trace Verification Reference.RiscV.Sail Reference.Sail
open Tests.ControlHistory

/-- Both aliasing x0 ports and the old x1 read use the initial instruction
    state; the decoded final port performs the actual link write. All segment
    states and the instruction's decoder entry come from the public claim. -/
theorem initialized_reads_write : ∃ after : State,
    run (SailRV32.Functions.rX_bits (.Regidx 0)) before = .ok (0 : BitVec 32) before ∧
    run (SailRV32.Functions.rX_bits (.Regidx 0)) before = .ok (0 : BitVec 32) before ∧
    run (SailRV32.Functions.rX_bits (.Regidx 1)) before = .ok (123 : BitVec 32) before ∧
    run (SailRV32.Functions.wX_bits (.Regidx 1) (4 : BitVec 32)) before = .ok () after := by
  have aligned : ∀ cell ∈ [Cell.register 0, Cell.register 1], cell.Aligned := by
    intro cell member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> simp [Cell.Aligned]
  obtain ⟨history, rows, after, _, permutation, _, _, _, transfers⟩ :=
    JumpBranchSlt.public_register_history ControlValues.decoder_image public_inputs
      accepted ControlValues.decoded aligned
  have singleton : rows = [nativeRow false] :=
    List.perm_singleton.mp (by simpa only [trace] using permutation)
  obtain ⟨entry, _, rowBefore, rowAfter, _, query, earlier, _, later, left, right, old, written⟩ :=
    transfers [] (nativeRow false) [] singleton
  change SailHistory _ [] before rowBefore at earlier
  change SailHistory _ [] rowAfter after at later
  cases earlier
  cases later
  obtain ⟨first, second, destination⟩ := Trace.Proofs.native_query_indices (by decide) query
  change 0 = entry.data.rs1.toNat at first
  change 0 = entry.data.rs2.toNat at second
  change 1 = entry.data.rd.toNat at destination
  have firstIndex : entry.data.rs1 = 0 := BitVec.eq_of_toNat_eq (by simpa using first.symm)
  have secondIndex : entry.data.rs2 = 0 := BitVec.eq_of_toNat_eq (by simpa using second.symm)
  have destinationIndex : entry.data.rd = 1 := BitVec.eq_of_toNat_eq (by simpa using destination.symm)
  have valueZero : (0 : ZMod mersenne31Modulus).val = 0 := by decide
  have valueLink : (4 : ZMod mersenne31Modulus).val = 4 := by decide
  have valueOld : (123 : ZMod mersenne31Modulus).val = 123 := by decide
  refine ⟨after, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [firstIndex, secondIndex, destinationIndex, MemoryPort.readCode, MemoryPort.writeCode,
      WordColumns.code, WordColumns.evaluate, JumpBranchSlt.importedConstraintsMemoryPorts,
      memoryWord, Nat.unpair_pair, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
      Arithmetic.limbBase, valueZero, valueLink, valueOld, nativeRow, assignment,
      Tests.JumpDecoder.assignment, Tests.JumpPC.negativeJal, Tests.JumpControl.assignment]
      at left right old written ⊢
  all_goals assumption

end Tests.ControlRegisters
