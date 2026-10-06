import Airbender.Review.AddSub.Discarded
import Airbender.Proofs.AddSub.PC
import Airbender.Proofs.Sail.PC

namespace Airbender.AddSub.Proofs
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

/-- Shared proof for all retained RTYPE/ITYPE clauses, including comparisons,
    bitwise operations and register shifts. Sail's x0 accessor discards the result. -/
theorem discarded_soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (Discarded.circuitModel (p := p)).SoundnessUnder
      Discarded.InterfaceAssumptions Discarded.spec := by
  rintro input finalPC w ⟨interfaces, constraints, mapping, _⟩
  obtain ⟨_, _, pc⟩ := pc_successor hp inverse constraints mapping interfaces.initialPCBounds
  apply Sail.retire_of_destination interfaces.pcRead pc
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC finalPC.toBitVec }
  have executed : run (Discarded.execution input.instruction) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS prepared := by
    cases hi : input.instruction with
    | register op rs1 rs2 =>
      obtain ⟨left, right, hl, hr⟩ := (show ∃ left right,
        run (SailRV32.Functions.rX_bits rs1) input.before = .ok left input.before ∧
        run (SailRV32.Functions.rX_bits rs2) input.before = .ok right input.before from
          by simpa only [hi] using interfaces.reads)
      have hl := Sail.rX_nextPC (pc := finalPC.toBitVec) rs1 hl
      have hr := Sail.rX_nextPC (pc := finalPC.toBitVec) rs2 hr
      cases op <;> simp only [Discarded.execution, SailRV32.Functions.execute_RTYPE,
        freeM_bind_assoc, freeM_pure_bind]
      all_goals rw [run_bind_of_ok _ _ _ _ _ hl, run_bind_of_ok _ _ _ _ _ hr,
        Sail.write_zero, freeM_pure_bind]
      all_goals rfl
    | immediate op rs1 imm =>
      obtain ⟨left, hl⟩ := (show ∃ left,
        run (SailRV32.Functions.rX_bits rs1) input.before = .ok left input.before from
          by simpa only [hi] using interfaces.reads)
      have hl := Sail.rX_nextPC (pc := finalPC.toBitVec) rs1 hl
      cases op <;> simp only [Discarded.execution, SailRV32.Functions.execute_ITYPE,
        freeM_bind_assoc, freeM_pure_bind]
      all_goals rw [run_bind_of_ok _ _ _ _ _ hl, Sail.write_zero, freeM_pure_bind]
      all_goals rfl
  refine ⟨prepared, executed, ?_⟩
  simp only [Sail.writeResult, Sail.write_zero, freeM_pure_bind]
  rfl

end Airbender.AddSub.Proofs
