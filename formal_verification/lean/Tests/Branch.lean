import Airbender.Review.JumpBranchSlt.Theorems
import Airbender.Proofs.Sail.ControlFlow

namespace Tests.Branch
open Airbender

-- BEQ, BNE, BLT, BGE, BLTU, BGEU on 0 and -1.
private def funct3 (tag : Fin 6) : Nat :=
  match tag.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 6 | _ => 7

private def taken (tag : Fin 6) : Bool := tag.val == 1 || tag.val == 3 || tag.val == 4

private def initial (wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨65532, 65535⟩ else ⟨0, 0⟩

private def offset (wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨8, 0⟩ else ⟨65532, 65535⟩

private def final (tag : Fin 6) (wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨if taken tag then 4 else 0, 0⟩
  else if taken tag then ⟨65532, 65535⟩ else ⟨4, 0⟩

private def row (tag : Fin 6) (wrap : Bool) : Nat → ZMod babyBearModulus
  | 0 => (initial wrap).lo
  | 1 => (initial wrap).hi
  | 4 | 5 | 14 | 15 | 34 | 37 | 38 => 1
  | 6 => 2
  | 8 => (offset wrap).lo
  | 9 => (offset wrap).hi
  | 10 => funct3 tag
  | 16 | 36 => (final tag wrap).lo
  | 17 => (final tag wrap).hi
  | 18 => 4
  | 26 | 27 | 43 => 65535
  | 39 | 40 => if wrap then 1 else 0
  | 44 | 45 => if taken tag then 1 else 0
  | _ => 0

set_option maxHeartbeats 800000 in
private theorem satisfies (tag : Fin 6) (wrap : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row tag wrap))
      JumpBranchSlt.importedConstraints := by
  fin_cases tag <;> cases wrap <;>
    simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, row, taken, initial, offset, final]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0, 0) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((1, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨1, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((65532, 0, 65532) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨65532, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((196607, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨196607, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((720895, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨720895, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((2293759, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨2293759, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((2818047, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨2818047, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((3342335, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨3342335, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((3866623, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨3866623, by decide⟩, rfl⟩)
    | decide

/-- Every real branch tag, with opposite signed/unsigned outcomes, has the
    resolved bit required by the local imported relation. -/
private theorem resolved (tag : Fin 6) (wrap : Bool) :
    row tag wrap 45 = if taken tag then 1 else 0 := by
  have result := JumpBranchSlt.branch_resolution (left := ⟨0, 0⟩)
    (right := ⟨65535, 65535⟩) (by decide) (satisfies tag wrap) rfl ⟨rfl, rfl, rfl⟩
    (by fin_cases tag <;> simp [row, funct3] <;> decide)
    ⟨rfl, rfl, rfl, rfl⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  convert result using 1
  fin_cases tag <;> cases wrap <;> decide

/-- Both branch outcomes and both PC boundaries: offset -4 at PC 0, and
    offset +8 at PC 0xfffffffc. This verifies local PC arithmetic, not Sail stepping. -/
example (tag : Fin 6) (wrap : Bool) :
    (final tag wrap).toBitVec =
      (if taken tag then (initial wrap).toBitVec + (offset wrap).toBitVec
        else (initial wrap).toBitVec + 4) ∧
      (final tag wrap).toBitVec.toNat % 4 = 0 := by
  apply JumpBranchSlt.branch_pc (w := row tag wrap) (by decide) (taken tag)
    (satisfies tag wrap) rfl ⟨rfl, rfl, rfl⟩ (resolved tag wrap)
  · constructor <;> cases wrap <;> cases ht : taken tag <;>
      simp [row, initial, offset, final, ht]
    all_goals decide
  · cases wrap <;> decide
  · cases wrap <;> decide
  · cases wrap <;> exact ⟨by decide, by decide⟩
  · cases wrap <;> decide
  · cases wrap <;> cases ht : taken tag <;> simp [final, ht] <;> decide

example (tag : Fin 6) (wrap : Bool) : row tag wrap 30 = 0 ∧ row tag wrap 31 = 0 :=
  JumpBranchSlt.masked_destination (satisfies tag wrap) rfl

private def input (tag : Fin 6) (wrap : Bool) : JumpBranchSlt.Branch.Input where
  opcode := match tag.val with
    | 0 => .BEQ | 1 => .BNE | 2 => .BLT | 3 => .BGE | 4 => .BLTU | _ => .BGEU
  left := ⟨0, 0⟩
  right := ⟨65535, 65535⟩
  offset := offset wrap
  pc := initial wrap
  rs1 := .Regidx 1
  rs2 := .Regidx 2
  encodedOffset := if wrap then 8 else 8188
  before := { (default : Reference.RiscV.Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (0 : BitVec 32) |>.insert .x2 (4294967295 : BitVec 32)
      |>.insert .x3 (37 : BitVec 32) |>.insert .nextPC (123 : BitVec 32)
      |>.insert .misa (if wrap then 0xffffffff else 0 : BitVec 32)
      |>.insert .PC (initial wrap).toBitVec) }

/-- Native Sail stepping for all six tags with real satisfying assignments.
    Covers both outcomes, signed/unsigned disagreement, -4 and wrapping +8,
    both compressed-extension settings and unrelated initialized registers. -/
example (tag : Fin 6) (wrap : Bool) :
    JumpBranchSlt.Branch.spec (input tag wrap) ⟨⟨0, 0⟩, final tag wrap⟩ := by
  apply JumpBranchSlt.Branch.babyBear_soundness _ _ (row tag wrap)
  refine ⟨?_, satisfies tag wrap, ?_⟩
  · constructor
    all_goals first
      | (apply Reference.RiscV.Sail.read_register
         fin_cases tag <;> cases wrap <;>
           simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
             Arithmetic.limbBase, Std.ExtDHashMap.get?_insert])
      | (refine ⟨if wrap then 0xffffffff else 0, ?_⟩
         apply Reference.RiscV.Sail.read_register
         simp [input, Std.ExtDHashMap.get?_insert])
      | (fin_cases tag <;> cases wrap <;> simp only [Arithmetic.Word.Bounded] <;> decide)
  · constructor <;> fin_cases tag <;> cases wrap <;> decide

private def equalRow (neq : Bool) : Nat → ZMod babyBearModulus
  | 4 | 14 | 15 | 41 => 1
  | 8 => 8
  | 10 => if neq then 1 else 0
  | 16 | 36 => if neq then 4 else 8
  | 18 => 4
  | 44 | 45 => if neq then 0 else 1
  | _ => 0

private theorem equalSatisfies (neq : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (equalRow neq))
      JumpBranchSlt.importedConstraints := by
  cases neq <;> simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, equalRow]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((0, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((8, 0, 8) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨8, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((262144, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨262144, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((786432, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨786432, by decide⟩, rfl⟩)

/-- The equality query is one exactly when the subtraction remainder is zero. -/
example (neq : Bool) : equalRow neq 45 = if neq then 0 else 1 := by
  have result := JumpBranchSlt.branch_resolution (left := ⟨0, 0⟩) (right := ⟨0, 0⟩)
    (by decide) (equalSatisfies neq) rfl ⟨rfl, rfl, rfl⟩
    (by cases neq <;> decide) ⟨rfl, rfl, rfl, rfl⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  convert result using 1
  cases neq <;> decide

private def misalignedRow (i : Nat) : ZMod babyBearModulus :=
  if i = 8 ∨ i = 36 then 2 else if i = 16 then 0 else if i = 46 then 1
  else equalRow false i

/-- A taken branch to PC 2 is rejected, even though cleanup would round it to 0.
    Four-byte target alignment was proved from the imported relation, not assumed. -/
example : ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment misalignedRow)
    JumpBranchSlt.importedConstraints := by
  intro h
  have pc := JumpBranchSlt.branch_pc (initial := ⟨0, 0⟩) (offset := ⟨2, 0⟩)
    (final := ⟨0, 0⟩) (by decide) true h rfl ⟨rfl, rfl, rfl⟩ rfl
    (by constructor <;> decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ (by decide) (by decide)
  exact (by decide : ¬ ((⟨0, 0⟩ : Arithmetic.Word).toBitVec =
    (⟨0, 0⟩ : Arithmetic.Word).toBitVec + (⟨2, 0⟩ : Arithmetic.Word).toBitVec)) pc.1

end Tests.Branch
