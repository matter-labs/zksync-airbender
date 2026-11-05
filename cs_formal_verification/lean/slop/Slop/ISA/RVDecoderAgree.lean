import Human.ISA.Sail.Airbender
import Human.Helpers.Decoder.RVPooledProgram

/-! Review aid for the RV program table (not on the RV proof path): on every word that `RV.decode` accepts, each
    native decoder projection on `RV.Instr` equals the Sail-typed one on `Airbender.toSail` of the decoded
    instruction. `Canon` records what `RV.decode` produces (immediate widths, load/store sizes); the agreement is then
    a case split on it. -/

namespace Airbender.RVDecoderAgree
open Arithmetic Trace

/-- The shapes `RV.decode` produces: immediates are sign extensions of their encoded widths (shift amounts: zero
    extensions of five bits; upper immediates: twenty bits and twelve zeros), and load/store sizes are 1, 2 or 4. -/
inductive Canon : RV.Instr → Prop
  | lui (rd : RV.Reg) (u : BitVec 20) : Canon (.lui rd (u ++ 0#12))
  | auipc (rd : RV.Reg) (u : BitVec 20) : Canon (.auipc rd (u ++ 0#12))
  | jal (rd : RV.Reg) (x : BitVec 21) : Canon (.jal rd (x.signExtend 32))
  | jalr (rd rs1 : RV.Reg) (x : BitVec 12) : Canon (.jalr rd rs1 (x.signExtend 32))
  | branch (c : RV.Cond) (rs1 rs2 : RV.Reg) (x : BitVec 13) : Canon (.branch c rs1 rs2 (x.signExtend 32))
  | load (n : Nat) (s : Bool) (rd rs1 : RV.Reg) (x : BitVec 12) (size : n = 1 ∨ n = 2 ∨ n = 4) :
      Canon (.load n s rd rs1 (x.signExtend 32))
  | store (n : Nat) (rs2 rs1 : RV.Reg) (x : BitVec 12) (size : n = 1 ∨ n = 2 ∨ n = 4) :
      Canon (.store n rs2 rs1 (x.signExtend 32))
  | opImm (op : RV.Op) (rd rs1 : RV.Reg) (x : BitVec 12) (notShift : op ≠ .sll ∧ op ≠ .srl ∧ op ≠ .sra) :
      Canon (.opImm op rd rs1 (x.signExtend 32))
  | shiftImm (op : RV.Op) (rd rs1 : RV.Reg) (x : BitVec 5) (shift : op = .sll ∨ op = .srl ∨ op = .sra) :
      Canon (.opImm op rd rs1 (x.zeroExtend 32))
  | op (op : RV.Op) (rd rs1 rs2 : RV.Reg) : Canon (.op op rd rs1 rs2)
  | mop (op : RV.FieldOp) (rd rs1 rs2 : RV.Reg) : Canon (.mop op rd rs1 rs2)
  | rev8 (rd rs1 : RV.Reg) : Canon (.rev8 rd rs1)
  | xorRot (n : BitVec 5) (rd rs1 : RV.Reg) : Canon (.xorRot n rd rs1)
  | inputRead (rd : RV.Reg) : Canon (.inputRead rd)
  | inputWrite (src : RV.Reg) : Canon (.inputWrite src)
  | delegate (k : RV.DelegationKind) : Canon (.delegate k)

theorem decode_canon {w : BitVec 32} {i : RV.Instr} (h : RV.decode w = some i) : Canon i := by
  unfold RV.decode at h
  dsimp only at h
  split at h
  all_goals (try simp only [RV.decodeCsr, RV.decodeMopR] at h)
  all_goals (try split_ifs at h)
  all_goals first | (cases h; done) | skip
  all_goals first
    | obtain rfl := Option.some.inj h
    | obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
  all_goals first
    | exact Canon.load _ _ _ _ _ (by decide)
    | exact Canon.store _ _ _ _ (by decide)
    | exact Canon.shiftImm _ _ _ _ (by simp)
    | exact Canon.opImm _ _ _ _ (by simp)
    | constructor

private theorem sext_low12 (x : BitVec 12) :
    SailRV32.Functions.sign_extend (m := 32) ((x.signExtend 32).extractLsb' 0 12) = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [SailRV32.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_extractLsb']
  by_cases h : j < 12 <;> simp [h, hj, BitVec.msb_eq_getLsbD_last, BitVec.getMsbD_eq_getLsbD,
    BitVec.getElem_signExtend]

private theorem sext_low13 (x : BitVec 13) :
    SailRV32.Functions.sign_extend (m := 32) ((x.signExtend 32).extractLsb' 0 13) = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [SailRV32.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_extractLsb']
  by_cases h : j < 13 <;> simp [h, hj, BitVec.msb_eq_getLsbD_last, BitVec.getMsbD_eq_getLsbD,
    BitVec.getElem_signExtend]

private theorem sext_low21 (x : BitVec 21) :
    SailRV32.Functions.sign_extend (m := 32) ((x.signExtend 32).extractLsb' 0 21) = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [SailRV32.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_extractLsb']
  by_cases h : j < 21 <;> simp [h, hj, BitVec.msb_eq_getLsbD_last, BitVec.getMsbD_eq_getLsbD,
    BitVec.getElem_signExtend]

private theorem upper_low (u : BitVec 20) : (u ++ 0#12).extractLsb' 12 20 = u := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [hj]
  rw [BitVec.getLsbD_append]
  simp [BitVec.getLsbD_eq_getElem hj]

theorem fields_agree {i : RV.Instr} (c : Canon i) : rvDecoderFields i = decoderFields (toSail i) := by
  cases c with
  | load n s rd rs1 x size =>
    rcases size with rfl | rfl | rfl <;> cases s <;> simp [rvDecoderFields, toSail, decoderFields, sext_low12]
  | store n rs2 rs1 x size =>
    rcases size with rfl | rfl | rfl <;> simp [rvDecoderFields, toSail, decoderFields, sext_low12]
  | opImm op rd rs1 x notShift =>
    cases op <;> simp_all [rvDecoderFields, toSail, decoderFields, sext_low12]
  | shiftImm op rd rs1 x shift =>
    rcases shift with rfl | rfl | rfl <;> simp [rvDecoderFields, toSail, decoderFields]
  | op op rd rs1 rs2 => cases op <;> rfl
  | _ => simp [rvDecoderFields, toSail, decoderFields, csrToSail, upper_low]

theorem jumpBranchSlt_agree {i : RV.Instr} (c : Canon i) :
    JumpBranchSlt.rvDecoderFields i = JumpBranchSlt.decoderFields (toSail i) := by
  cases c with
  | branch cond rs1 rs2 x =>
    cases cond <;> simp [JumpBranchSlt.rvDecoderFields, toSail, JumpBranchSlt.decoderFields, sext_low13,
      sailBranchOp, JumpBranchSlt.Branch.rvFunct3, JumpBranchSlt.Branch.funct3]
  | load n s rd rs1 x size =>
    rcases size with rfl | rfl | rfl <;> cases s <;> simp [JumpBranchSlt.rvDecoderFields, toSail,
      JumpBranchSlt.decoderFields]
  | store n rs2 rs1 x size =>
    rcases size with rfl | rfl | rfl <;> simp [JumpBranchSlt.rvDecoderFields, toSail, JumpBranchSlt.decoderFields]
  | opImm op rd rs1 x notShift =>
    cases op <;> simp_all [JumpBranchSlt.rvDecoderFields, toSail, JumpBranchSlt.decoderFields, sext_low12]
  | shiftImm op rd rs1 x shift =>
    rcases shift with rfl | rfl | rfl <;> simp [JumpBranchSlt.rvDecoderFields, toSail, JumpBranchSlt.decoderFields]
  | op op rd rs1 rs2 => cases op <;> rfl
  | _ => simp [JumpBranchSlt.rvDecoderFields, toSail, JumpBranchSlt.decoderFields, csrToSail, sext_low12,
      sext_low21]

theorem mulDiv_agree {i : RV.Instr} (c : Canon i) :
    MulDiv.rvDecoderFields i = MulDiv.decoderFields (toSail i) := by
  cases c with
  | load n s rd rs1 x size =>
    rcases size with rfl | rfl | rfl <;> cases s <;> simp [MulDiv.rvDecoderFields, toSail, MulDiv.decoderFields]
  | store n rs2 rs1 x size =>
    rcases size with rfl | rfl | rfl <;> simp [MulDiv.rvDecoderFields, toSail, MulDiv.decoderFields]
  | opImm op rd rs1 x notShift =>
    cases op <;> simp_all [MulDiv.rvDecoderFields, toSail, MulDiv.decoderFields]
  | shiftImm op rd rs1 x shift =>
    rcases shift with rfl | rfl | rfl <;> simp [MulDiv.rvDecoderFields, toSail, MulDiv.decoderFields]
  | op op rd rs1 rs2 => cases op <;> rfl
  | _ => simp [MulDiv.rvDecoderFields, toSail, MulDiv.decoderFields, csrToSail]

theorem shiftBinop_agree {i : RV.Instr} (c : Canon i) :
    ShiftBinop.rvDecoderFields i = ShiftBinop.decoderFields (toSail i) := by
  cases c with
  | load n s rd rs1 x size =>
    rcases size with rfl | rfl | rfl <;> cases s <;> simp [ShiftBinop.rvDecoderFields, toSail,
      ShiftBinop.decoderFields]
  | store n rs2 rs1 x size =>
    rcases size with rfl | rfl | rfl <;> simp [ShiftBinop.rvDecoderFields, toSail, ShiftBinop.decoderFields]
  | opImm op rd rs1 x notShift =>
    cases op <;> simp_all [ShiftBinop.rvDecoderFields, toSail, ShiftBinop.decoderFields, sext_low12]
  | shiftImm op rd rs1 x shift =>
    have hx : x.toNat % 4294967296 = x.toNat := Nat.mod_eq_of_lt (by have := x.isLt; omega)
    rcases shift with rfl | rfl | rfl <;> simp [ShiftBinop.rvDecoderFields, toSail, ShiftBinop.decoderFields, hx]
  | op op rd rs1 rs2 => cases op <;> rfl
  | _ => simp [ShiftBinop.rvDecoderFields, toSail, ShiftBinop.decoderFields, csrToSail]

theorem subwordMemory_agree {i : RV.Instr} (c : Canon i) :
    SubwordMemory.rvDecoderFields i = SubwordMemory.decoderFields (toSail i) := by
  cases c with
  | load n s rd rs1 x size =>
    rcases size with rfl | rfl | rfl <;> cases s <;> simp [SubwordMemory.rvDecoderFields, toSail,
      SubwordMemory.decoderFields, sext_low12]
  | store n rs2 rs1 x size =>
    rcases size with rfl | rfl | rfl <;> simp [SubwordMemory.rvDecoderFields, toSail, SubwordMemory.decoderFields,
      sext_low12]
  | opImm op rd rs1 x notShift =>
    cases op <;> simp_all [SubwordMemory.rvDecoderFields, toSail, SubwordMemory.decoderFields]
  | shiftImm op rd rs1 x shift =>
    rcases shift with rfl | rfl | rfl <;> simp [SubwordMemory.rvDecoderFields, toSail, SubwordMemory.decoderFields]
  | op op rd rs1 rs2 => cases op <;> rfl
  | _ => simp [SubwordMemory.rvDecoderFields, toSail, SubwordMemory.decoderFields, csrToSail]

/-- On every word `RV.decode` accepts, the six RV projections equal the Sail-typed ones on `toSail`. -/
theorem decoder_agree {w : BitVec 32} {i : RV.Instr} (h : RV.decode w = some i) :
    rvDecoderFields i = decoderFields (toSail i) ∧
    JumpBranchSlt.rvDecoderFields i = JumpBranchSlt.decoderFields (toSail i) ∧
    MulDiv.rvDecoderFields i = MulDiv.decoderFields (toSail i) ∧
    ShiftBinop.rvDecoderFields i = ShiftBinop.decoderFields (toSail i) ∧
    SubwordMemory.rvDecoderFields i = SubwordMemory.decoderFields (toSail i) ∧
    rvPooledDecoderFields i = pooledDecoderFields (toSail i) := by
  have c := decode_canon h
  have a := fields_agree c
  have b := jumpBranchSlt_agree c
  have m := mulDiv_agree c
  have s := shiftBinop_agree c
  have u := subwordMemory_agree c
  refine ⟨a, b, m, s, u, ?_⟩
  unfold rvPooledDecoderFields pooledDecoderFields
  rw [a, b, m, s, u]

end Airbender.RVDecoderAgree
