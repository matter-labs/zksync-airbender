import Airbender.Review.JumpBranchSlt.Theorems
import Airbender.Proofs.Sail.ControlFlow

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

set_option maxHeartbeats 800000 in
theorem satisfies (indirect wrap zero : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row indirect wrap zero))
      JumpBranchSlt.importedConstraints := by
  cases indirect <;> cases wrap <;> cases zero <;>
    simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, row, initial, offset, base, final]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((65535, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨65535, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((0, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((4, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((393216, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨393216, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((458752, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨458752, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((65532, 0, 65532) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨65532, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((1, 0, 0) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨1, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((5, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨5, by decide⟩, rfl⟩)
    | decide

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
  apply JumpBranchSlt.Jump.babyBear_soundness _ _ (row indirect wrap zero)
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
