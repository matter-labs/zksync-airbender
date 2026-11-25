module
public import Proven.UnifiedReduced.RV.Step
public import Proven.Final.Circuits.UnifiedReduced.Proth120Modular
public import Proven.UnifiedReduced.Modular.Frame
public import Proven.UnifiedReduced.Proth120.Setup
public import Human.Circuits.UnifiedReduced.Proth120Execution

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Arithmetic Trace

def modularEntry (op : AddSub.Modular.Opcode) (rs1 rs2 rd : _root_.RV.Reg) : DecoderData UnifiedFamily :=
  ⟨.machine, rs1, rs2, rd, ⟨0, 0⟩, 2 ^ (op.selector - 10), 0⟩

/-- The wrap decoder extends the ordinary registry by its four emulated BabyBear operations. -/
theorem decoded_cases {i : _root_.RV.Instr} {data : DecoderData UnifiedFamily}
    (h : decoderFields i = some data) : rvDecoderFields i = some data ∨
    ∃ (op : AddSub.Modular.Opcode) (rs1 rs2 rd : _root_.RV.Reg),
      i = .mop op.rvOp rd rs1 rs2 ∧ data = modularEntry op rs1 rs2 rd := by
  unfold decoderFields at h
  cases orig : rvDecoderFields i with
  | some d =>
    left
    simpa [orig] using h
  | none =>
    right
    rw [orig] at h
    cases i <;> try cases h
    rename_i o rd r1 r2
    cases o <;> cases h
    · exact ⟨.add, _, _, _, rfl, rfl⟩
    · exact ⟨.sub, _, _, _, rfl, rfl⟩
    · exact ⟨.mul, _, _, _, rfl, rfl⟩
    · exact ⟨.fma, _, _, _, rfl, rfl⟩

/-- The instruction's three register reads, single write and PC increment come from the same row. -/
theorem modular_step {cells epoch w before after} (inputs : RowInputs cells epoch w before after)
    (op : AddSub.Modular.Opcode) (rs1 rs2 rd : _root_.RV.Reg)
    (entry : UnifiedReduced.RVProgramEntry) (pc : before.pc = entry.pc)
    (data : entry.data = modularEntry op rs1 rs2 rd) (query : decoderQuery w = entry.query) :
    ∃ next, exec before (.mop op.rvOp rd rs1 rs2) = some next ∧ _root_.RV.Same next
      { after with pc := (wordAt w 30).toBitVec } := by
  have small : entry.data.mask < 512 := by rw [data]; cases op <;> norm_num [modularEntry, AddSub.Modular.Opcode.selector]
  obtain ⟨flags, _, left, right, old, written, finish⟩ := UnifiedReduced.Standard.Modular.Proofs.row_frame (profile := .proth120) (by decide)
    (full_setup_holds inputs.constraints) inputs.active query small pc inputs.history
  rw [data] at flags left right old written
  change before.getReg rs1 = (wordAt w 36).toBitVec at left
  change before.getReg rs2 = (wordAt w 42).toBitVec at right
  change before.getReg rd = (wordAt w 48).toBitVec at old
  have setting (k : Nat) (lo : 11 ≤ k) (hi : k ≤ 20) :
      w k = if k = op.selector + 1 then 1 else 0 := by
    have flag := flags ⟨k - 11, by omega⟩
    rw [show 11 + (k - 11) = k by omega] at flag
    change w k = (if (2 ^ (op.selector - 10) : Nat).testBit (k - 11) then 1 else 0) at flag
    rw [Nat.testBit_two_pow] at flag
    have sel : 10 ≤ op.selector := by cases op <;> decide
    simpa only [decide_eq_true_eq,
      show (op.selector - 10 = k - 11) ↔ k = op.selector + 1 by omega] using flag
  have value := modular_result _ _ op inputs.constraints setting
    inputs.bounded.1 inputs.bounded.2.1 inputs.bounded.2.2
  dsimp only at value
  rw [← left, ← right, ← old] at value
  refine ⟨_, _root_.RV.exec_mop before op.rvOp rd rs1 rs2, ?_⟩
  rw [← value]
  exact UnifiedReduced.Standard.Proofs.RV.rv_register_next written finish

end Airbender.UnifiedReduced.Proth120
