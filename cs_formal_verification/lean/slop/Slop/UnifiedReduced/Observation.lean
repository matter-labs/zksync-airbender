import Human.Circuits.UnifiedReduced.Model
import Human.Circuits.UnifiedReduced.Control
import Human.Circuits.UnifiedReduced.Jump
import Human.Circuits.UnifiedReduced.Shift
import Human.Circuits.UnifiedReduced.WordMemory

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

inductive Observation where
  | arithmetic (input : Input)
  | jump (input : Jump.Input)
  | branch (input : Control.Branch.Input)
  | comparison (input : Control.Comparison.Input)
  | binary (shift : Bool) (input : Binary.Input)
  | memory (input : Airbender.WordMemory.Input)

def observe (w : Nat → ZMod p) (before : State) (instruction : SailRV32.instruction) : Option Observation :=
  let left := Control.leftWord w
  let right := Control.rightWord w
  let immediate := Control.offsetWord w
  let pc := Control.initialPC w
  let arithmetic op rs1 rs2 rd imm upper :=
    some (.arithmetic ⟨⟨op, left, right, immediate, pc⟩, rs1, rs2, rd, imm, upper, before⟩)
  let comparison op rs1 rs2 rd imm :=
    some (.comparison ⟨op, left, Control.comparisonRight w, pc, rs1, rs2, rd, imm, before⟩)
  let binary shift op isImmediate rs1 rs2 rd imm :=
    some (.binary shift ⟨op, isImmediate, left.toBitVec,
      if isImmediate then SailRV32.Functions.sign_extend (m := 32) imm else right.toBitVec,
      pc, rs1, rs2, rd, imm, before⟩)
  match instruction with
  | .RTYPE (rs2, rs1, rd, .ADD) => arithmetic .add rs1 rs2 rd 0 0
  | .RTYPE (rs2, rs1, rd, .SUB) => arithmetic .sub rs1 rs2 rd 0 0
  | .ITYPE (imm, rs1, rd, .ADDI) => arithmetic .addi rs1 zeroRegister rd imm 0
  | .UTYPE (imm, rd, .LUI) => arithmetic .lui zeroRegister zeroRegister rd 0 imm
  | .UTYPE (imm, rd, .AUIPC) => arithmetic .auipc zeroRegister zeroRegister rd 0 imm
  | .JAL (imm, rd) => some (.jump ⟨.jal imm, left, immediate, pc, zeroRegister, rd, before⟩)
  | .JALR (imm, rs1, rd) => some (.jump ⟨.jalr imm, left, immediate, pc, rs1, rd, before⟩)
  | .BTYPE (imm, rs2, rs1, op) => some (.branch ⟨op, left, right, immediate, pc, rs1, rs2, imm, before⟩)
  | .RTYPE (rs2, rs1, rd, .SLT) => comparison .slt rs1 rs2 rd 0
  | .RTYPE (rs2, rs1, rd, .SLTU) => comparison .sltu rs1 rs2 rd 0
  | .ITYPE (imm, rs1, rd, .SLTI) => comparison .slti rs1 zeroRegister rd imm
  | .ITYPE (imm, rs1, rd, .SLTIU) => comparison .sltiu rs1 zeroRegister rd imm
  | .RTYPE (rs2, rs1, rd, .XOR) => binary false .xor false rs1 rs2 rd 0
  | .RTYPE (rs2, rs1, rd, .OR) => binary false .or false rs1 rs2 rd 0
  | .RTYPE (rs2, rs1, rd, .AND) => binary false .and false rs1 rs2 rd 0
  | .ITYPE (imm, rs1, rd, .XORI) => binary false .xor true rs1 zeroRegister rd imm
  | .ITYPE (imm, rs1, rd, .ORI) => binary false .or true rs1 zeroRegister rd imm
  | .ITYPE (imm, rs1, rd, .ANDI) => binary false .and true rs1 zeroRegister rd imm
  | .RTYPE (rs2, rs1, rd, .SLL) => binary true .sll false rs1 rs2 rd 0
  | .RTYPE (rs2, rs1, rd, .SRL) => binary true .srl false rs1 rs2 rd 0
  | .RTYPE (rs2, rs1, rd, .SRA) => binary true .sra false rs1 rs2 rd 0
  | .SHIFTIOP (imm, rs1, rd, .SLLI) => binary true .sll true rs1 zeroRegister rd (imm.zeroExtend 12)
  | .SHIFTIOP (imm, rs1, rd, .SRLI) => binary true .srl true rs1 zeroRegister rd (imm.zeroExtend 12)
  | .SHIFTIOP (imm, rs1, rd, .SRAI) => binary true .sra true rs1 zeroRegister rd (imm.zeroExtend 12)
  | .REV8 (rs1, rd) => binary true .rev8 false rs1 zeroRegister rd 0
  | .LOAD (imm, rs1, rd, false, 4) => some (.memory ⟨false, left, immediate, right, pc, rs1, zeroRegister, rd, imm, before⟩)
  | .STORE (imm, rs2, rs1, 4) => some (.memory ⟨true, left, immediate, right, pc, rs1, rs2, zeroRegister, imm, before⟩)
  | _ => none

theorem observe_supported {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (w : Nat → ZMod p) (before : State) (fields : decoderFields instruction = some data) :
    ∃ result, observe w before instruction = some result := by
  unfold observe
  split
  all_goals first | (exact ⟨_, rfl⟩) | skip
  unfold decoderFields at fields
  cases first : Trace.decoderFields instruction with
  | some original =>
    unfold Trace.decoderFields at first
    split at first <;> grind
  | none =>
    cases second : JumpBranchSlt.decoderFields instruction with
    | some original =>
      unfold JumpBranchSlt.decoderFields at second
      split at second <;> grind
    | none =>
      cases third : ShiftBinop.decoderFields instruction with
      | none => simp [first, second, third] at fields
      | some original =>
        unfold ShiftBinop.decoderFields at third
        split at third <;> grind

end Airbender.UnifiedReduced.Proofs
