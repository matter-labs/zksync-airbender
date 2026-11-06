import Slop.JumpBranchSlt.Claims
import Slop.Sail.ControlFlow
import Slop.JumpBranchSlt.Completeness.Witness

namespace Tests.Jump
open Airbender

private def initial (wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨65532, 65535⟩ else ⟨0, 0⟩

private def base (indirect wrap : Bool) : Arithmetic.Word :=
  if indirect then (if wrap then ⟨65535, 65535⟩ else ⟨5, 0⟩) else initial wrap

private def offset (indirect wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨if indirect then 6 else 8, 0⟩ else ⟨65532, 65535⟩

private def final (indirect wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨4, 0⟩ else if indirect then ⟨0, 0⟩ else ⟨65532, 65535⟩

def row (indirect wrap zero : Bool) : Nat → ZMod babyBearModulus
  | 0 => (initial wrap).lo
  | 1 => (initial wrap).hi
  | 4 => 1
  | 5 => if indirect then 1 else 0
  | 7 => if zero then 0 else 1
  | 8 => (offset indirect wrap).lo
  | 9 => (offset indirect wrap).hi
  | 11 => if indirect then 0 else 1
  | 12 => if indirect then 1 else 0
  | 15 => if zero then 1 else 0
  | 16 => (final indirect wrap).lo
  | 17 => (final indirect wrap).hi
  | 18 => 4
  | 22 => if indirect then (base indirect wrap).lo else 0
  | 23 => if indirect then (base indirect wrap).hi else 0
  | 30 => if zero || wrap then 0 else 4
  | 34 | 47 => if wrap then 0 else 4
  | 36 => if wrap then (if indirect then 5 else 4) else (if indirect then 1 else 65532)
  | 37 | 38 | 41 | 44 => if wrap then 1 else 0
  | 39 | 40 => if indirect || wrap then 1 else 0
  | 42 => if indirect && wrap then 1 else 0
  | _ => 0

/-- The honest inputs `row` is built from: the operands, PC and offset; zero clocks. -/
private def witness (indirect wrap zero : Bool) : JumpBranchSlt.Completeness.Inputs where
  sel := if indirect then 1 else 0
  rdZero := zero
  funct3 := 0
  rs1 := if indirect then 1 else 0
  rs2 := 0
  rd := if zero then 0 else 1
  pcLo := (initial wrap).lo
  pcHi := (initial wrap).hi
  aLo := if indirect then (base indirect wrap).lo else 0
  aHi := if indirect then (base indirect wrap).hi else 0
  bLo := 0
  bHi := 0
  immLo := (offset indirect wrap).lo
  immHi := (offset indirect wrap).hi
  oldLo := 0
  oldHi := 0
  tsLo := 0
  tsHi := 0
  prev0Lo := 0
  prev0Hi := 0
  prev1Lo := 0
  prev1Hi := 0
  prev2Lo := 0
  prev2Hi := 0
  borrow0 := 0
  borrow1 := 0
  borrow2 := 0

private theorem valid (indirect wrap zero : Bool) : (witness indirect wrap zero).Valid := by
  cases indirect <;> cases wrap <;> cases zero <;> constructor <;> decide

private theorem agree (indirect wrap zero : Bool) : ∀ i ∈ JumpBranchSlt.Completeness.columns,
    row indirect wrap zero i = (witness indirect wrap zero).honest i := by
  cases indirect <;> cases wrap <;> cases zero <;> decide

theorem satisfies (indirect wrap zero : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row indirect wrap zero))
      JumpBranchSlt.importedConstraints :=
  JumpBranchSlt.Completeness.complete_of_agree _ (valid indirect wrap zero) (agree indirect wrap zero)

/-- Eight imported rows: JAL/JALR, PC+4 and target wrapping, x0/nonzero rd.
    JALR's sums are odd; their bit-0 cleanup is exercised explicitly. -/
example (indirect wrap zero : Bool) :
    (⟨(row indirect wrap zero 30).val, (row indirect wrap zero 31).val⟩ : Arithmetic.Word).toBitVec =
      (if row indirect wrap zero 15 = 1 then 0 else (initial wrap).toBitVec + 4) ∧
    (⟨(row indirect wrap zero 30).val, (row indirect wrap zero 31).val⟩ : Arithmetic.Word).Bounded := by
  apply JumpBranchSlt.Proofs.jump_link (by decide) (satisfies indirect wrap zero)
  · cases indirect <;> simp [row]
  · exact ⟨rfl, rfl⟩
  · constructor <;> cases wrap <;> simp [row, initial] <;> decide
  · cases wrap <;> decide

example (indirect wrap zero : Bool) :
    (final indirect wrap).toBitVec =
      (if indirect then ((base indirect wrap).toBitVec + (offset indirect wrap).toBitVec) &&& 0xfffffffe
        else (base indirect wrap).toBitVec + (offset indirect wrap).toBitVec) ∧
      (final indirect wrap).toBitVec.toNat % 4 = 0 := by
  apply JumpBranchSlt.Proofs.jump_pc (w := row indirect wrap zero) (by decide) indirect
    (satisfies indirect wrap zero) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  · constructor <;> cases indirect <;> cases wrap <;>
      simp [row, initial, base, offset, final] <;> decide
  · cases indirect <;> cases wrap <;> decide
  · cases indirect <;> cases wrap <;> decide
  · cases indirect <;> cases wrap <;> exact ⟨by decide, by decide⟩
  · cases indirect <;> cases wrap <;> decide
  · cases indirect <;> cases wrap <;> decide

private def input (indirect wrap zero : Bool) : JumpBranchSlt.Jump.Input where
  instruction := if indirect then .jalr (if wrap then 6 else 4092)
    else .jal (if wrap then 8 else 2097148)
  source := if indirect then base indirect wrap else ⟨0, 0⟩
  offset := offset indirect wrap
  pc := initial wrap
  rs1 := if indirect then .Regidx 1 else .Regidx 0
  rd := if zero then .Regidx 0 else .Regidx 1
  before := { (default : Reference.RiscV.Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (base true wrap).toBitVec |>.insert .x2 (39 : BitVec 32)
      |>.insert .nextPC (123 : BitVec 32) |>.insert .PC (initial wrap).toBitVec
      |>.insert .misa (if wrap then 0xffffffff else 0 : BitVec 32)
      |>.insert .cur_privilege .Machine |>.insert .mseccfg (0 : BitVec 64)
      |>.insert .elp (1 : BitVec 1)) }

private def output (indirect wrap zero : Bool) : Reference.RiscV.Sail.Output :=
  ⟨⟨if zero || wrap then 0 else 4, 0⟩, final indirect wrap⟩

/-- Native JAL/JALR on eight satisfying assignments: target/link wrapping,
    negative offsets, odd JALR sums, rd/rs1 aliasing and discarded x0 writes.
    The initialized elp bit is preserved under Machine-mode MLPE-clear execution. -/
example (indirect wrap zero : Bool) :
    JumpBranchSlt.Jump.spec (input indirect wrap zero) (output indirect wrap zero) := by
  apply JumpBranchSlt.Jump.babyBear_row_soundness _ _ (row indirect wrap zero)
  refine ⟨?_, satisfies indirect wrap zero, ?_⟩
  · constructor
    all_goals first
      | (apply Reference.RiscV.Sail.read_register
         cases indirect <;> cases wrap <;> cases zero <;>
           simp [input, Std.ExtDHashMap.get?_insert])
      | (refine ⟨if wrap then 0xffffffff else 0, ?_⟩
         apply Reference.RiscV.Sail.read_register
         simp [input, Std.ExtDHashMap.get?_insert])
      | (intro selected
         cases indirect
         · simp [input, JumpBranchSlt.Jump.Instruction.indirect] at selected
         · apply Reference.RiscV.Sail.read_register
           cases wrap <;> cases zero <;> simp [input, Std.ExtDHashMap.get?_insert])
      | (intro selected
         cases indirect
         · simp [input, JumpBranchSlt.Jump.Instruction.indirect] at selected
         · refine ⟨Reference.RiscV.Sail.read_register (by simp [input, Std.ExtDHashMap.get?_insert]),
             0, Reference.RiscV.Sail.read_register (by simp [input, Std.ExtDHashMap.get?_insert]), ?_⟩
           decide)
      | (cases indirect <;> cases wrap <;> cases zero <;>
         try simp only [Arithmetic.Word.Bounded]
         all_goals decide)
  · constructor <;> cases indirect <;> cases wrap <;> cases zero <;> decide

private def misalignedRow (i : Nat) : ZMod babyBearModulus :=
  if i = 22 then 7 else if i = 36 then 3 else if i = 46 then 1 else row true false false i

/-- Clearing bit 0 of 7+(-4) gives PC 2, rejected by the imported bit-1 check. -/
example : ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment misalignedRow)
    JumpBranchSlt.importedConstraints := by
  intro h
  have target := JumpBranchSlt.Proofs.jump_pc (base := ⟨7, 0⟩) (offset := ⟨65532, 65535⟩)
    (final := ⟨0, 0⟩) (by decide) true h ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (by constructor <;> decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ (by decide) (by decide)
  exact (by decide : ¬ ((⟨0, 0⟩ : Arithmetic.Word).toBitVec =
    ((⟨7, 0⟩ : Arithmetic.Word).toBitVec + (⟨65532, 65535⟩ : Arithmetic.Word).toBitVec) &&& 0xfffffffe)) target.1

end Tests.Jump
