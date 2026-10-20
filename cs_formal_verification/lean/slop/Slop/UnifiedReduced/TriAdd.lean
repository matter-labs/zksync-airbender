import Slop.UnifiedReduced.TriAddCalculation
import Slop.UnifiedReduced
import Slop.Sail.PC

namespace Airbender.UnifiedReduced.Proofs
open Airbender.Reference.RiscV
open Airbender.Reference.Sail
open Airbender.Arithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

private theorem triadd_result {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {setup : Table (ZMod p) (fields 10)} {input : TriAdd.Input} {output : Sail.Output}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (interfaces : TriAdd.Calculation.InterfaceAssumptions input output w)
    (mapping : TriAdd.Calculation.WordMapping input output w) (nonzero : input.rd ≠ Sail.zeroRegister) :
    output.destination.toBitVec = input.oldDestination.toBitVec + input.left.toBitVec + input.right.toBitVec := by
  have selected := interfaces.selected
  simp only [nonzero, if_false] at selected
  have other := dispatch_exclusive (by omega) h interfaces.active 9 selected
  have s11 : w 11 = 0 := other 0 (by decide)
  have s12 : w 12 = 0 := other 1 (by decide)
  have s13 : w 13 = 0 := other 2 (by decide)
  have s14 : w 14 = 0 := other 3 (by decide)
  have s15 : w 15 = 0 := other 4 (by decide)
  have s16 : w 16 = 0 := other 5 (by decide)
  have s17 : w 17 = 0 := other 6 (by decide)
  have s20 : w 20 = 1 := selected
  have operands := mapping.operands nonzero
  have outLo : w 50 = (output.destination.lo : ZMod p) := by
    rw [mapping.outputLo]; exact (ZMod.natCast_zmod_val _).symm
  have outHi : w 51 = (output.destination.hi : ZMod p) := by
    rw [mapping.outputHi]; exact (ZMod.natCast_zmod_val _).symm
  have lo := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    s11, s12, s13, s14, s15, s16, s17, s20, operands.1, operands.2.1,
    operands.2.2.1, operands.2.2.2.1, operands.2.2.2.2.1, operands.2.2.2.2.2, outLo, outHi] at lo hi
  have ranges := interfaces.ranges nonzero
  have outputRanges := destination_bounds h
  have cb1 : (w 53).val ≤ 1 := boolean_val (local_flags h 21)
  have cb2 : (w 54).val ≤ 1 := boolean_val (local_flags h 22)
  have wb1 : (w 52).val ≤ 1 := boolean_val (local_flags h 20)
  have wb2 : (w 55).val ≤ 1 := boolean_val (local_flags h 23)
  apply Word.add_of_limbs hp ranges.2.2 ranges.1 ranges.2.1
    ⟨mapping.outputLo ▸ outputRanges.1, mapping.outputHi ▸ outputRanges.2⟩
    (carry := (w 53).val + (w 54).val) (wrap := (w 52).val + (w 55).val)
    (by omega) (by omega)
  · simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    linear_combination lo
  · simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    linear_combination hi

private theorem triadd_contract_nextPC {input : TriAdd.Input}
    (hc : TriAdd.Calculation.RegisterContract input) (pc : BitVec 32) :
    TriAdd.Calculation.RegisterContract { input with before :=
      { input.before with regs := input.before.regs.insert .nextPC pc } } := by
  constructor
  · obtain ⟨value, read, mapping⟩ := hc.leftRead
    exact ⟨value, Sail.rX_nextPC input.rs1 read, mapping⟩
  · obtain ⟨value, read, mapping⟩ := hc.rightRead
    exact ⟨value, Sail.rX_nextPC input.rs2 read, mapping⟩
  · obtain ⟨value, read, mapping⟩ := hc.oldRead
    exact ⟨value, Sail.rX_nextPC input.rd read, mapping⟩
  · exact Sail.read_register_nextPC pc (by decide) hc.pcRead

private theorem triadd_destination {input : TriAdd.Input} {output : Word}
    (hc : TriAdd.Calculation.RegisterContract input)
    (result : input.rd ≠ Sail.zeroRegister →
      output.toBitVec = input.oldDestination.toBitVec + input.left.toBitVec + input.right.toBitVec) :
    ∃ after,
      run (TriAdd.execution input) input.before = .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
      run (Sail.writeResult input.rd output) input.before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  obtain ⟨left, hl, ml⟩ := hc.leftRead
  obtain ⟨right, hr, mr⟩ := hc.rightRead
  obtain ⟨old, ho, mo⟩ := hc.oldRead
  by_cases hz : input.rd = Sail.zeroRegister
  · refine ⟨input.before, ?_, ?_⟩
    · simp only [TriAdd.execution, TriAdd.clause]
      rw [run_bind_of_ok _ _ _ _ _ hl, run_bind_of_ok _ _ _ _ _ hr,
        run_bind_of_ok _ _ _ _ _ ho, hz, Sail.write_zero, freeM_pure_bind]
      rfl
    · rw [Sail.writeResult, hz, Sail.write_zero, freeM_pure_bind]
      rfl
  · rw [ml hz] at hl
    rw [mr hz] at hr
    rw [mo hz] at ho
    have executed : run (TriAdd.execution input) input.before = run (Sail.writeResult input.rd output) input.before := by
      simp only [TriAdd.execution, TriAdd.clause, Sail.writeResult]
      rw [run_bind_of_ok _ _ _ _ _ hl, run_bind_of_ok _ _ _ _ _ hr,
        run_bind_of_ok _ _ _ _ _ ho, ← result hz]
    obtain ⟨after, written⟩ := Sail.write_success input.rd output.toBitVec input.before
    have projected : run (Sail.writeResult input.rd output) input.before =
        .ok SailRV32.Functions.RETIRE_SUCCESS after := by
      rw [Sail.writeResult, run_bind_of_ok _ _ _ _ _ written]
      rfl
    exact ⟨after, executed.trans projected, projected⟩

theorem triadd_soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (setup : Table (ZMod p) (fields 10)) :
    (TriAdd.Calculation.circuitModel setup).SoundnessUnder TriAdd.Calculation.InterfaceAssumptions TriAdd.spec := by
  rintro input output w ⟨interfaces, constraints, mapping⟩
  have other := dispatch_exclusive (by omega) constraints interfaces.active
    (if input.rd = Sail.zeroRegister then 0 else 9) interfaces.selected
  have outside : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 := by
    repeat' apply And.intro
    all_goals first
      | (apply other 10; split <;> decide)
      | (apply other 11; split <;> decide)
      | (apply other 12; split <;> decide)
      | (apply other 13; split <;> decide)
  have pcHi : w 1 = (input.pc.hi : ZMod p) := by
    rw [mapping.pcHi]; exact (ZMod.natCast_zmod_val _).symm
  have pc := pc_successor (by omega) constraints interfaces.active outside
    ⟨mapping.pcLo, pcHi, mapping.finalPCLo, mapping.finalPCHi⟩
    ⟨interfaces.initialPCLoBound, mapping.pcHi ▸ initial_pc_hi_bound constraints⟩
  apply Sail.retire_of_destination interfaces.registers.pcRead pc.2.2
  apply triadd_destination (triadd_contract_nextPC interfaces.registers output.pc.toBitVec)
  intro nonzero
  exact triadd_result (input := input) hp constraints interfaces mapping nonzero

end Airbender.UnifiedReduced.Proofs
