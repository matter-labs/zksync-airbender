import Tests.AirbenderProgram
import Airbender.Proofs.Trace.FiniteFootprint
import Airbender.Proofs.Trace.ImageInstall
import Airbender.Review.Trace.Initialization

namespace Tests.AirbenderNative
open Airbender Airbender.Trace Airbender.Arithmetic Airbender.Initialization
open Airbender.Reference Airbender.Reference.Sail Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

/-- Actual native assignments for the four public instructions. The three ports
refresh a shared register/RAM history at clocks4/5/6,8/9/10,12/13/14,16/17/18. -/
def luiAssignment : Nat → ZMod babyBearModulus
  | 2 | 19 | 27 => 4
  | 21 => 8
  | 4 | 7 | 10 | 42 | 43 | 44 => 1
  | 9 | 34 => 512
  | _ => 0

def addiAssignment : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 19 | 27 => 8
  | 21 => 12
  | 4 | 10 | 42 | 43 | 44 => 1
  | 7 => 2
  | 8 | 33 => 7
  | 23 => 5
  | _ => 0

def swAssignment : Nat → ZMod babyBearModulus
  | 0 => 8
  | 2 | 11 => 12
  | 13 => 16
  | 4 | 5 | 10 | 44 | 46 | 47 | 48 => 1
  | 6 | 19 => 2
  | 15 => 6
  | 18 | 26 => 512
  | 21 => 10
  | 23 | 31 => 7
  | 36 => 448
  | 38 => 33554432
  | _ => 0

def lwAssignment : Nat → ZMod babyBearModulus
  | 0 | 15 => 12
  | 2 | 11 => 16
  | 13 => 20
  | 4 | 5 | 44 | 46 | 47 | 48 => 1
  | 7 | 25 => 3
  | 18 | 20 => 512
  | 21 => 14
  | 23 | 31 => 7
  | 36 => 448
  | 38 => 33554432
  | _ => 0

def rows : List (Row babyBearModulus PooledFamily) :=
  [⟨.addSub, luiAssignment⟩, ⟨.addSub, addiAssignment⟩,
   ⟨.wordMemory, swAssignment⟩, ⟨.wordMemory, lwAssignment⟩]

private theorem lui_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment luiAssignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, luiAssignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)
    | norm_num [babyBearModulus]

private theorem addi_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment addiAssignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, addiAssignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)
    | norm_num [babyBearModulus]

private theorem sw_constraints (rom : Table (ZMod babyBearModulus) (fields 9))
    (disabled : rom.Contains #[] (Vector.replicate 9 0)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment swAssignment)
      (WordMemory.clockConstraints rom) := by
  simp [WordMemory.clockConstraints, WordMemory.importedConstraints,
    WordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, swAssignment, Lookup.Contains, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | exact disabled
    | decide
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)

private theorem lw_constraints (rom : Table (ZMod babyBearModulus) (fields 9))
    (disabled : rom.Contains #[] (Vector.replicate 9 0)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment lwAssignment)
      (WordMemory.clockConstraints rom) := by
  simp [WordMemory.clockConstraints, WordMemory.importedConstraints,
    WordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, lwAssignment, Lookup.Contains, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | exact disabled
    | decide
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)

/-- Only five cells are touched. The full selected native domain remains a
symbolic list, and untouched tokens cancel by FiniteFootprint.balance_of_nodup. -/
def touched : List Cell := [.register 0, .register 1, .register 2, .register 3, .ram 33554432]

def old (cell : Cell) : MemoryToken babyBearModulus := cell.initialToken 0

def final (cell : Cell) : MemoryToken babyBearModulus :=
  if cell = .register 0 then ⟨cell.addressCode, (9, 0), Nat.pair 0 0⟩
  else if cell = .register 1 then ⟨cell.addressCode, (16, 0), Nat.pair 0 512⟩
  else if cell = .register 2 then ⟨cell.addressCode, (13, 0), Nat.pair 7 0⟩
  else if cell = .register 3 then ⟨cell.addressCode, (18, 0), Nat.pair 7 0⟩
  else if cell = .ram 33554432 then ⟨cell.addressCode, (17, 0), Nat.pair 7 0⟩
  else old cell

def pooledProgram : List PooledProgramEntry :=
  AirbenderProgram.program.map (ProgramEntry.mapFamily pooledArithmeticFamily)

noncomputable def trace (domain : List Cell) (physical : List (MemoryToken babyBearModulus)) :
    PooledTrace babyBearModulus where
  rows := rows
  rom := ⟨ROM.table domain physical, Verification.subwordTable (ROM.words AirbenderProgram.before)⟩
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 16 (20, 0)
  initialMemory := domain.map old
  terminalMemory := domain.map final

private theorem disabled (domain : List Cell) (physical : List (MemoryToken babyBearModulus)) :
    (ROM.table domain physical).Contains #[] (Vector.replicate 9 0) := by
  change ∃ index : Fin (ROM.rows domain physical).length,
    Vector.replicate 9 0 = (ROM.rows domain physical).get index
  exact ⟨⟨0, by simp [ROM.rows]⟩, rfl⟩

theorem accepted (domain : List Cell) (physical : List (MemoryToken babyBearModulus))
    (distinct : domain.Nodup) (subset : touched ⊆ domain) : Accepted (trace domain physical) := by
  constructor
  · intro row member
    change row ∈ rows at member
    simp only [rows, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact lui_constraints
    · exact addi_constraints
    · exact sw_constraints _ (disabled domain physical)
    · exact lw_constraints _ (disabled domain physical)
  · intro row member
    change row ∈ rows at member
    simp only [rows, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  · change ([PCState.boundary 0 (4, 0)] ++ rows.map Row.finish).Perm
      ([PCState.boundary 16 (20, 0)] ++ rows.map Row.start)
    change ([PCState.boundary 0 (4, 0), PCState.boundary 4 (8, 0),
      PCState.boundary 8 (12, 0), PCState.boundary 12 (16, 0)] ++
      [PCState.boundary 16 (20, 0)]).Perm
      ([PCState.boundary 16 (20, 0)] ++ [PCState.boundary 0 (4, 0),
        PCState.boundary 4 (8, 0), PCState.boundary 8 (12, 0), PCState.boundary 12 (16, 0)])
    exact List.perm_append_comm
  · apply Trace.FiniteFootprint.balance_of_nodup domain touched old final
      (rows.flatMap Row.reads) (rows.flatMap Row.writes) distinct (by decide) subset
    · intro cell _ outside
      dsimp only [final]
      split_ifs
      all_goals first
        | rfl
        | (exfalso; apply outside; subst cell; decide)
    · decide

theorem decoded (domain : List Cell) (physical : List (MemoryToken babyBearModulus)) :
    PooledDecoded (trace domain physical) pooledProgram := by
  intro row member
  change row ∈ rows at member
  simp only [rows, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨⟨0, by decide⟩, by decide⟩
  · exact ⟨⟨1, by decide⟩, by decide⟩
  · exact ⟨⟨0, by decide⟩, by decide⟩
  · exact ⟨⟨1, by decide⟩, by decide⟩

end Tests.AirbenderNative
