module
public import Proven.UnifiedReduced.RV.Arith
public import Proven.UnifiedReduced.RV.Family3
public import Proven.UnifiedReduced.RV.Control
public import Proven.UnifiedReduced.RV.Jump
public import Proven.UnifiedReduced.RV.Memory
public import Proven.ISA.RV.DecodeShape

@[expose] public section

/-! Every row of the unified RV table steps (`row_step`): the case split over `rvDecoderFields`. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

private theorem low_five (b : RV.Word) : (b.setWidth 5).toNat = (b.extractLsb' 0 5).toNat := by
  simp [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]

private theorem small_five {b : RV.Word} (small : b.toNat < 32) : (b.setWidth 5).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt small

private theorem binary_data {o : ShiftBinop.Operation} {rs1 rs2 rd : RV.Reg} {imm : Word} {j : DecoderData Unit}
    (fields : ShiftBinop.instructionFields o rs1 rs2 rd imm = some j) (binary : o.isShift = false) :
    binaryFields j = ⟨.machine, rs1, rs2, rd, imm, 65536, Setup.binaryTag o.tag⟩ := by
  unfold ShiftBinop.instructionFields at fields
  split at fields
  · cases fields
  · obtain rfl := Option.some.inj fields
    cases o <;> simp_all [binaryFields, DecoderData.mapFamily, Setup.binaryTag, ShiftBinop.Operation.tag,
      ShiftBinop.Operation.isShift]

private theorem shift_data {o : ShiftBinop.Operation} {rs1 rs2 rd : RV.Reg} {imm : Word} {j : DecoderData Unit}
    (fields : ShiftBinop.instructionFields o rs1 rs2 rd imm = some j) (shift : o.isShift = true) :
    binaryFields j = ⟨.machine, rs1, rs2, rd, imm, 32768, o.tag⟩ := by
  unfold ShiftBinop.instructionFields at fields
  split at fields
  · cases fields
  · obtain rfl := Option.some.inj fields
    cases o <;> simp_all [binaryFields, DecoderData.mapFamily, ShiftBinop.Operation.isShift]

private theorem binary_immediate_shape {bits : RV.Word} {op : RV.Op} {rd rs1 : RV.Reg} {imm : RV.Word}
    (decodes : RV.decode bits = some (.opImm op rd rs1 imm)) (binary : op = .xor ∨ op = .or ∨ op = .and) :
    ∃ x : BitVec 12, imm = x.signExtend 32 := by
  have shape := RV.decode_shape decodes
  simp only [RV.Shape] at shape
  rcases shape with ⟨_, x, hx⟩ | ⟨kind, _⟩
  · exact ⟨x, hx⟩
  · rcases binary with rfl | rfl | rfl <;> simp at kind

/-- Shift and binary rows. -/
theorem family_three_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State}
    {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) {j : DecoderData Unit}
    (binary : ShiftBinop.rvDecoderFields i = some j) (data : entry.data = binaryFields j) :
    RowStep w s after i := by
  unfold ShiftBinop.rvDecoderFields at binary
  split at binary
  · exact binary_reg_step hp byteInverse facts (by decide) (fun _ _ => by simp [RV.alu, Verification.byteOperation, ShiftBinop.Operation.tag])
      (data.trans (binary_data binary rfl))
  · exact binary_reg_step hp byteInverse facts (by decide) (fun _ _ => by simp [RV.alu, Verification.byteOperation, ShiftBinop.Operation.tag])
      (data.trans (binary_data binary rfl))
  · exact binary_reg_step hp byteInverse facts (by decide) (fun _ _ => by simp [RV.alu, Verification.byteOperation, ShiftBinop.Operation.tag])
      (data.trans (binary_data binary rfl))
  · rename_i rd rs1 rs2
    refine shift_step hp byteInverse facts (by decide) (data.trans (shift_data binary rfl)) (Or.inr rfl)
      (fun h => absurd h (by decide)) ?_
    intro n _ register
    refine ⟨_, RV.exec_op s .sll rd rs1 rs2, ?_⟩
    rw [register (Or.inr rfl)]
    simp only [RV.alu, low_five]
    exact RV.Same.refl _
  · rename_i rd rs1 rs2
    refine shift_step hp byteInverse facts (by decide) (data.trans (shift_data binary rfl)) (Or.inr rfl)
      (fun h => absurd h (by decide)) ?_
    intro n _ register
    refine ⟨_, RV.exec_op s .srl rd rs1 rs2, ?_⟩
    rw [register (Or.inr rfl)]
    simp only [RV.alu, low_five]
    exact RV.Same.refl _
  · rename_i rd rs1 rs2
    refine shift_step hp byteInverse facts (by decide) (data.trans (shift_data binary rfl)) (Or.inr rfl)
      (fun h => absurd h (by decide)) ?_
    intro n _ register
    refine ⟨_, RV.exec_op s .sra rd rs1 rs2, ?_⟩
    rw [register (Or.inr rfl)]
    simp only [RV.alu, low_five]
    exact RV.Same.refl _
  · obtain ⟨x, rfl⟩ := binary_immediate_shape facts.decodes (Or.inl rfl)
    exact binary_imm_step hp byteInverse facts (by decide) (fun _ _ => by simp [RV.alu, Verification.byteOperation, ShiftBinop.Operation.tag])
      (data.trans (binary_data binary rfl))
  · obtain ⟨x, rfl⟩ := binary_immediate_shape facts.decodes (Or.inr (Or.inl rfl))
    exact binary_imm_step hp byteInverse facts (by decide) (fun _ _ => by simp [RV.alu, Verification.byteOperation, ShiftBinop.Operation.tag])
      (data.trans (binary_data binary rfl))
  · obtain ⟨x, rfl⟩ := binary_immediate_shape facts.decodes (Or.inr (Or.inr rfl))
    exact binary_imm_step hp byteInverse facts (by decide) (fun _ _ => by simp [RV.alu, Verification.byteOperation, ShiftBinop.Operation.tag])
      (data.trans (binary_data binary rfl))
  · rename_i rd rs1 imm
    split at binary
    · rename_i small
      refine shift_step hp byteInverse facts (by decide) (data.trans (shift_data binary rfl))
        (Or.inl ⟨rfl, rfl, small⟩) (fun h => absurd h (by decide)) ?_
      intro n immediate _
      refine ⟨_, RV.exec_opImm s .sll rd rs1 imm, ?_⟩
      rw [immediate rfl]
      simp only [RV.alu, small_five small]
      exact RV.Same.refl _
    · cases binary
  · rename_i rd rs1 imm
    split at binary
    · rename_i small
      refine shift_step hp byteInverse facts (by decide) (data.trans (shift_data binary rfl))
        (Or.inl ⟨rfl, rfl, small⟩) (fun h => absurd h (by decide)) ?_
      intro n immediate _
      refine ⟨_, RV.exec_opImm s .srl rd rs1 imm, ?_⟩
      rw [immediate rfl]
      simp only [RV.alu, small_five small]
      exact RV.Same.refl _
    · cases binary
  · rename_i rd rs1 imm
    split at binary
    · rename_i small
      refine shift_step hp byteInverse facts (by decide) (data.trans (shift_data binary rfl))
        (Or.inl ⟨rfl, rfl, small⟩) (fun h => absurd h (by decide)) ?_
      intro n immediate _
      refine ⟨_, RV.exec_opImm s .sra rd rs1 imm, ?_⟩
      rw [immediate rfl]
      simp only [RV.alu, small_five small]
      exact RV.Same.refl _
    · cases binary
  · refine shift_step hp byteInverse facts (by decide) (data.trans (shift_data binary rfl)) (Or.inr rfl)
      (fun _ => ⟨rfl, rfl⟩) ?_
    intro n immediate _
    refine ⟨_, rfl, ?_⟩
    rw [immediate rfl]
    exact RV.Same.refl _
  · cases binary

/-- Jump/branch/comparison rows. -/
theorem control_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State}
    {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) {j : DecoderData Unit}
    (jump : JumpBranchSlt.rvDecoderFields i = some j) (data : entry.data = jumpFields j) :
    RowStep w s after i := by
  have jbs := jump
  unfold JumpBranchSlt.rvDecoderFields at jump
  split at jump
  · rename_i rd rs1 rs2
    split at jump
    · cases jump
    · obtain rfl := Option.some.inj jump
      exact comparison_step hp ⟨.slt, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩ rfl facts data jbs
  · rename_i rd rs1 rs2
    split at jump
    · cases jump
    · obtain rfl := Option.some.inj jump
      exact comparison_step hp ⟨.sltu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩ rfl facts data jbs
  · rename_i rd rs1 imm
    split at jump
    · cases jump
    · obtain rfl := Option.some.inj jump
      have shape := RV.decode_shape facts.decodes
      simp only [RV.Shape] at shape
      rcases shape with ⟨_, x, rfl⟩ | ⟨kind, _⟩
      · exact comparison_step hp ⟨.slti, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, s⟩ rfl facts data jbs
      · simp at kind
  · rename_i rd rs1 imm
    split at jump
    · cases jump
    · obtain rfl := Option.some.inj jump
      have shape := RV.decode_shape facts.decodes
      simp only [RV.Shape] at shape
      rcases shape with ⟨_, x, rfl⟩ | ⟨kind, _⟩
      · exact comparison_step hp ⟨.sltiu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, s⟩ rfl facts data jbs
      · simp at kind
  · rename_i cond rs1 rs2 offset
    obtain rfl := Option.some.inj jump
    obtain ⟨x, rfl⟩ := RV.decode_shape facts.decodes
    exact branch_step hp ⟨cond, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, x, s⟩ rfl facts data jbs
  · obtain rfl := Option.some.inj jump
    exact jal_step hp facts data
  · obtain rfl := Option.some.inj jump
    exact jalr_step hp facts data
  · cases jump

/-- ADD/SUB/ADDI/LUI/AUIPC, LW and SW rows. -/
theorem word_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State}
    {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) (nop : rvNopWrite i = false)
    (word : rvWordFields i = some entry.data) :
    RowStep w s after i := by
  by_cases small : entry.data.mask < 1024
  · exact arith_step hp facts word small
  have fields := word
  unfold rvWordFields at word
  split at word
  all_goals try (have d := (Option.some.inj word).symm; rw [d] at small; simp at small; done)
  · rename_i rd rs1 imm
    have nonzero : rd ≠ 0 := by simpa [rvNopWrite] using nop
    exact lw_step hp facts nonzero (Option.some.inj word).symm
  · exact sw_step hp facts (Option.some.inj word).symm
  · cases word

/-- TRIADD and XORROT rows. -/
theorem custom_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State}
    {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) (custom : rvCustomFields i = some entry.data) :
    RowStep w s after i := by
  unfold rvCustomFields at custom
  split at custom
  · exact triadd_step hp facts (Option.some.inj custom).symm
  · rename_i n rd rs1
    obtain ⟨tag, found, data⟩ := Option.map_eq_some_iff.mp custom
    exact xorrot_step hp byteInverse facts found data.symm
  · cases custom

/-- Every row of the RV table takes one `RV.exec` step that agrees with its history and final PC. -/
theorem row_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State}
    {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) :
    RowStep w s after i := by
  rcases rv_fields_cases facts.fields with ⟨nop, data⟩ | ⟨nop, word⟩ | ⟨_, _, j, jump, data⟩ |
      ⟨_, _, _, j, binary, data⟩ | ⟨_, _, _, _, custom⟩
  · exact nop_step hp facts nop data
  · exact word_step hp facts nop word
  · exact control_step hp facts jump data
  · exact family_three_step hp byteInverse facts binary data
  · exact custom_step hp byteInverse facts custom

end Airbender.UnifiedReduced.Proofs.RV
