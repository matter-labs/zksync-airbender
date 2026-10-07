import Airbender.Review.JumpBranchSlt.Theorems

namespace Tests.Comparison
open Airbender

/-- A selected SLTU row with zero operands and correct lookup results, but an
    unbounded final-PC high limb. This is a local-interface counterexample, not a
    claim that the full decoder/ROM/execution arguments accept the row. -/
private def row : Nat → ZMod babyBearModulus
  | 4 | 7 | 13 | 40 | 41 => 1
  | 10 => 3
  | 16 | 18 | 36 => 4
  | 17 => 2013200385
  | _ => 0

theorem unboundedFinalPCSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((0, 1) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((1835008, 0) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨1835008, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | decide

example : ¬ ((⟨4, (row 17).val⟩ : Arithmetic.Word).toBitVec =
    (⟨0, 0⟩ : Arithmetic.Word).toBitVec + 4) := by decide

/-- The malformed local row cannot be an outgoing PC in the logical global
    interface, for any program or terminal boundary. Cryptographic enforcement
    of this interface is not claimed here. -/
theorem unboundedFinalPCNotComposable {n : Nat}
    (context : PCState.Context babyBearModulus n)
    (outgoing : PCState.Outgoing context (row 16, row 17)) : ¬ PCState.Interface context := by
  intro global
  have bounds := JumpBranchSlt.final_pc_bounds (by decide) global outgoing unboundedFinalPCSatisfies
  exact (by decide : ¬ (row 17).val < Arithmetic.limbBase) bounds.2

private def edgeRow (signed immediate wrapPC : Bool) : Nat → ZMod babyBearModulus
  | 0 => if wrapPC then 65532 else 0
  | 1 => if wrapPC then 65535 else 0
  | 4 | 5 | 13 | 34 | 37 | 38 => 1
  | 30 | 44 | 47 => if signed then 0 else 1
  | 6 => if immediate then 0 else 2
  | 7 => if immediate then 1 else 2
  | 8 | 9 => if immediate then 65535 else 0
  | 10 => if signed then 2 else 3
  | 16 | 36 => if wrapPC then 0 else 4
  | 18 => 4
  | 39 | 40 => if wrapPC then 1 else 0
  | 26 | 27 => if immediate then 0 else 65535
  | 43 => 65535
  | _ => 0

set_option maxHeartbeats 600000 in
private theorem edgeSatisfies (signed immediate wrapPC : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (edgeRow signed immediate wrapPC))
      JumpBranchSlt.importedConstraints := by
  cases signed <;> cases immediate <;> cases wrapPC <;> simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, edgeRow]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((1, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨1, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((1769471, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨1769471, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((1245183, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨1245183, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus),
             ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0, 0) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus),
             ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | decide

/-- Unsigned 0 < 0xffffffff requires both subtraction borrows and resolves to one. -/
example : (⟨(edgeRow false false false 30).val, (edgeRow false false false 31).val⟩ : Arithmetic.Word).value = 1 := by
  have result := JumpBranchSlt.Proofs.unsigned_destination (p := babyBearModulus) (by decide)
    (left := ⟨0, 0⟩) (right := ⟨65535, 65535⟩) (edgeSatisfies false false false)
    rfl ⟨rfl, rfl, rfl⟩ rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (output := ⟨(edgeRow false false false 30).val, (edgeRow false false false 31).val⟩)
    ⟨rfl, rfl⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  simpa [Arithmetic.Word.value, Arithmetic.limbBase] using result

private def input (signed immediate wrapPC : Bool) : JumpBranchSlt.Comparison.Input where
  opcode := if signed then (if immediate then .slti else .slt)
    else (if immediate then .sltiu else .sltu)
  left := ⟨0, 0⟩
  right := ⟨65535, 65535⟩
  pc := if wrapPC then ⟨65532, 65535⟩ else ⟨0, 0⟩
  rs1 := .Regidx 1
  rs2 := if immediate then .Regidx 0 else .Regidx 2
  rd := if immediate then .Regidx 1 else .Regidx 2
  encodedImmediate := if immediate then 4095 else 0
  before := { (default : Reference.RiscV.Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (0 : BitVec 32) |>.insert .x2 (4294967295 : BitVec 32)
      |>.insert .PC (if wrapPC then 4294967292 else 0 : BitVec 32)) }

private def output (signed wrapPC : Bool) : Reference.RiscV.Sail.Output :=
  ⟨⟨if signed then 0 else 1, 0⟩, if wrapPC then ⟨0, 0⟩ else ⟨4, 0⟩⟩

/-- All four comparisons against -1 (including its immediate encoding),
    with source/destination aliases and 32-bit PC
    wraparound, obtained from concrete satisfying imported assignments. -/
example (signed immediate wrapPC : Bool) : JumpBranchSlt.Comparison.spec (input signed immediate wrapPC) (output signed wrapPC) := by
  apply JumpBranchSlt.Comparison.babyBear_soundness (input signed immediate wrapPC) (output signed wrapPC) (edgeRow signed immediate wrapPC)
  refine ⟨?_, edgeSatisfies signed immediate wrapPC, ?_⟩
  · constructor
    all_goals solve
      | (apply Reference.RiscV.Sail.read_register
         cases signed <;> cases immediate <;> cases wrapPC <;> simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
           Arithmetic.limbBase, Std.ExtDHashMap.get?_insert])
      | (change Arithmetic.Word.Bounded ⟨0, 0⟩; exact ⟨by decide, by decide⟩)
      | (change Arithmetic.Word.Bounded ⟨65535, 65535⟩; exact ⟨by decide, by decide⟩)
      | (intro hop
         cases signed <;> cases immediate <;> cases wrapPC
         all_goals solve
           | (rcases hop with hop | hop <;> cases hop)
           | (apply Reference.RiscV.Sail.read_register
              simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
                Arithmetic.limbBase, Std.ExtDHashMap.get?_insert])
           | decide)
      | (cases signed <;> cases immediate <;> cases wrapPC <;> (try dsimp [input]) <;> decide)
  · constructor <;> cases signed <;> cases immediate <;> cases wrapPC <;> rfl

private def negativeRow : Nat → ZMod babyBearModulus
  | 4 | 5 | 7 | 13 | 30 | 42 | 44 | 47 => 1
  | 6 | 10 => 2
  | 16 | 18 | 36 => 4
  | 22 | 23 | 34 | 35 => 65535
  | _ => 0

private theorem negativeSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment negativeRow)
      JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, negativeRow]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((131070, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨131070, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((65535, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨65535, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((1114112, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨1114112, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus),
             ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)

private def negativeInput : JumpBranchSlt.Comparison.Input :=
  { (input false false false) with
    opcode := .slt
    left := ⟨65535, 65535⟩
    right := ⟨0, 0⟩
    rd := .Regidx 1
    before :=
      { (default : Reference.RiscV.Sail.State) with regs :=
        ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
          |>.insert .x1 (4294967295 : BitVec 32) |>.insert .x2 (0 : BitVec 32)
          |>.insert .PC (0 : BitVec 32)) } }

/-- -1 < 0 signed, although the unsigned borrow is zero; rd aliases rs1. -/
example : JumpBranchSlt.Comparison.spec negativeInput (output false false) := by
  apply JumpBranchSlt.Comparison.babyBear_soundness negativeInput (output false false) negativeRow
  refine ⟨?_, negativeSatisfies, ?_⟩
  · constructor
    all_goals solve
      | (simp only [negativeInput, input]
         apply Reference.RiscV.Sail.read_register
         simp [Arithmetic.Word.toBitVec, Arithmetic.Word.value,
           Arithmetic.limbBase, Std.ExtDHashMap.get?_insert])
      | (change Arithmetic.Word.Bounded ⟨0, 0⟩; exact ⟨by decide, by decide⟩)
      | (change Arithmetic.Word.Bounded ⟨65535, 65535⟩; exact ⟨by decide, by decide⟩)
      | (intro hop
         solve
           | (rcases hop with hop | hop <;> cases hop)
           | (simp only [negativeInput, input]
              apply Reference.RiscV.Sail.read_register
              simp [Arithmetic.Word.toBitVec, Arithmetic.Word.value,
                Arithmetic.limbBase, Std.ExtDHashMap.get?_insert]))
      | ((try dsimp [negativeInput, input]) <;> decide)
  · constructor <;> simp [negativeRow, negativeInput, input, output] <;> decide

end Tests.Comparison
