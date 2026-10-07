import Airbender.Review.JumpBranchSlt.Branch
import Airbender.Proofs.JumpBranchSlt.Branch
import Airbender.Proofs.Sail.ControlFlow

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

/-- The pure comparison appearing inside the generated execute_BTYPE clause. -/
private def nativeCondition (op : SailRV32.bop) (left right : BitVec 32) : Bool :=
  match op with
  | .BEQ => left == right | .BNE => left != right
  | .BLT => SailRV32.Functions.zopz0zI_s left right
  | .BGE => SailRV32.Functions.zopz0zKzJ_s left right
  | .BLTU => SailRV32.Functions.zopz0zI_u left right
  | .BGEU => SailRV32.Functions.zopz0zKzJ_u left right

private theorem resolved_native {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {input : Branch.Input} {output : Sail.Output} {w : Nat → ZMod p}
    (interface : Branch.InterfaceAssumptions input output w)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : Branch.WordMapping input output w) :
    w 45 = if nativeCondition input.opcode input.left.toBitVec input.right.toBitVec then 1 else 0 := by
  have tag : (w 10).val = Branch.funct3 input.opcode := by
    have small : Branch.funct3 input.opcode < p := by
      cases input.opcode <;> simp only [Branch.funct3] <;> omega
    rw [interface.conditionTag, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt small
  have tagBound : (w 10).val ≤ 7 := by rw [tag]; cases input.opcode <;> decide
  have result := branch_resolution hp h interface.selected interface.otherSelectors
    tagBound mapping.operands interface.leftBound interface.rightBound
  rw [tag] at result
  cases op : input.opcode <;>
    simpa [op, Branch.funct3, nativeCondition, SailRV32.Functions.zopz0zI_s,
      SailRV32.Functions.zopz0zKzJ_s, SailRV32.Functions.zopz0zI_u,
      SailRV32.Functions.zopz0zKzJ_u, _root_.Sail.BitVec.toNatInt,
      Word.toBitVec_toNat interface.leftBound, Word.toBitVec_toNat interface.rightBound] using result

/-- All six branches: imported resolution and PC equations establish the actual
    Sail register/PC transition, including taken targets and not-taken PC+4. -/
theorem branch_soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    Branch.circuitModel.SoundnessUnder (Branch.InterfaceAssumptions (p := p)) Branch.spec := by
  intro input output w ⟨interface, h, mapping⟩
  let taken := nativeCondition input.opcode input.left.toBitVec input.right.toBitVec
  obtain ⟨pc, aligned⟩ := branch_pc hp taken h interface.selected interface.otherSelectors
    (resolved_native hp interface h mapping) mapping.pcOffset interface.initialPCLoBound
    interface.pcAligned interface.offsetBound interface.offsetEven interface.finalPCHiBound
  apply Sail.retire_of_effects interface.pcRead
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC (input.pc.toBitVec + 4) }
  let written : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have leftRead := Sail.rX_nextPC (pc := input.pc.toBitVec + 4) input.rs1 interface.leftRead
  have rightRead := Sail.rX_nextPC (pc := input.pc.toBitVec + 4) input.rs2 interface.rightRead
  have pcRead := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide)
    (show run (SailRV32.readReg .PC) input.before = .ok input.pc.toBitVec input.before from interface.pcRead)
  have reduced : run (Branch.execution input) prepared =
      run (if taken then SailRV32.Functions.jump_to
        (input.pc.toBitVec + SailRV32.Functions.sign_extend (m := 32) input.encodedOffset)
        else pure SailRV32.Functions.RETIRE_SUCCESS) prepared := by
    cases op : input.opcode <;>
      simp only [Branch.execution, op, SailRV32.Functions.execute_BTYPE,
        freeM_bind_assoc, freeM_pure_bind]
    all_goals rw [run_bind_of_ok _ _ _ _ _ leftRead, run_bind_of_ok _ _ _ _ _ rightRead]
    all_goals simp only [taken, nativeCondition, op]
    all_goals split
    all_goals first | (rw [run_bind_of_ok _ _ _ _ _ pcRead]) | rfl
  have executed : run (Branch.execution input) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS written := by
    rw [reduced]
    cases condition : taken
    · simp only [condition, Bool.false_eq_true, ↓reduceIte] at pc ⊢
      simp only [prepared, written, pc]
      rfl
    · simp only [condition, ↓reduceIte] at pc ⊢
      obtain ⟨misa, read⟩ := interface.misaRead
      have read' := Sail.read_register_nextPC (input.pc.toBitVec + 4) (by decide) read
      rw [← interface.signExtension, ← pc]
      simpa only [prepared, written, Sail.nextPC_overwrite] using
        Sail.jump_to_aligned aligned read'
  refine ⟨written, executed, ?_⟩
  simp only [Sail.writeResult, Sail.write_zero, freeM_pure_bind]
  rfl

end Airbender.JumpBranchSlt.Proofs
