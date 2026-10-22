import Human.RV32

/-! What a decoded instruction looks like (`Shape`): the immediates' widths, the operations each format allows, the
CSR rows' registers. The only place besides `Slop/Equiv/Decode.lean` that splits the decoder table: proofs by
instruction kind use `decode_shape` and case on the instruction, so a new decoder row of an existing shape changes
nothing downstream. -/

namespace RV

def Shape : Instr → Prop
  | .lui _ imm | .auipc _ imm => ∃ u : BitVec 20, imm = u ++ (0 : BitVec 12)
  | .jal _ off => ∃ x : BitVec 21, off = x.signExtend 32
  | .jalr _ _ off => ∃ x : BitVec 12, off = x.signExtend 32
  | .branch _ _ _ off => ∃ x : BitVec 13, off = x.signExtend 32
  | .load n _ _ _ off => (n = 1 ∨ n = 2 ∨ n = 4) ∧ ∃ x : BitVec 12, off = x.signExtend 32
  | .store n _ _ off => (n = 1 ∨ n = 2 ∨ n = 4) ∧ ∃ x : BitVec 12, off = x.signExtend 32
  | .opImm o _ _ imm =>
      ((o = .add ∨ o = .slt ∨ o = .sltu ∨ o = .xor ∨ o = .or ∨ o = .and) ∧ ∃ x : BitVec 12, imm = x.signExtend 32) ∨
      ((o = .sll ∨ o = .srl ∨ o = .sra) ∧ ∃ sh : BitVec 5, imm = sh.zeroExtend 32)
  | .op o _ _ _ => (o = .add ∨ o = .sub ∨ o = .sll ∨ o = .slt ∨ o = .sltu ∨ o = .xor ∨ o = .srl ∨ o = .sra ∨
      o = .or ∨ o = .and) ∨ (o = .mul ∨ o = .mulhu ∨ o = .divu ∨ o = .remu)
  | .mop .. | .rev8 .. | .xorRot .. => True
  | .inputRead rd => rd ≠ 0
  | .inputWrite src => src ≠ 0
  | .delegate _ => True

theorem decode_shape {w : Word} {i : Instr} (h : decode w = some i) : Shape i := by
  unfold decode at h
  simp only at h
  split at h
  all_goals (try simp only [decodeCsr, decodeMopR] at h)
  all_goals (try split_ifs at h)
  all_goals first
    | (cases h; done)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; trivial)
    | skip
  all_goals obtain rfl := Option.some.inj h
  all_goals simp only [Shape]
  all_goals first
    | trivial
    | exact ⟨_, rfl⟩
    | exact ⟨by simp, _, rfl⟩
    | (left; exact ⟨by simp, _, rfl⟩)
    | (right; exact ⟨by simp, _, rfl⟩)
    | simp_all

end RV
