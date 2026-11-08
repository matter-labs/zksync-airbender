import Slop.Trace.Claims
import Slop.Trace.NativeSailHistory
import Slop.Trace.Terminal
import Slop.Trace.RowContext

namespace Tests.TraceStore
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

-- SW x2,4(x1), crossing a limb boundary. Native state starts at PC 65532,
-- clock four; the three imported ports refresh x1/x2 and write RAM at 4259840.
private def assignment : Nat → ZMod babyBearModulus
  | 0 | 17 => 65532
  | 2 | 8 => 4
  | 13 => 8
  | 4 | 5 | 10 | 12 | 33 | 36 | 44 | 46 | 47 | 48 => 1
  | 6 | 19 => 2
  | 18 => 64
  | 23 | 31 => 1234
  | 24 | 32 => 5678
  | 26 => 65
  | 38 => 4259840
  | _ => 0

private def row : Row babyBearModulus := ⟨.wordMemory, assignment⟩
private def regToken (index time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair index 0), (time, 0), Nat.pair lo hi⟩
private def ramToken (loAddress hiAddress time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨Nat.pair 1 (Nat.pair loAddress hiAddress), (time, 0), Nat.pair lo hi⟩
private def initial : List (MemoryToken babyBearModulus) :=
  [regToken 1 0 65532 64, regToken 2 0 1234 5678, ramToken 0 65 0 0 0]
private def rom : Table (ZMod babyBearModulus) (fields 9) :=
  ROM.table [.register 1, .register 2, .ram 4259840] initial
private def trace : Data babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := initial
  terminalMemory := [regToken 1 4 65532 64, regToken 2 5 1234 5678, ramToken 0 65 6 1234 5678]

theorem local_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (WordMemory.clockConstraints rom) := by
  simp [WordMemory.clockConstraints, WordMemory.importedConstraints,
    WordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment, Lookup.Contains, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (change ∃ i : Fin 1, _
       exact ⟨0, rfl⟩)

theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact local_satisfies
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [trace, initial]
    decide

private theorem boundary : ClockBoundary trace := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro token member
    simp [trace, initial] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

private theorem aligned_domain :
    ∀ cell : Cell, cell ∈ [.register 1, .register 2, .ram 4259840] → cell.Aligned := by
  intro cell member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl <;> trivial

private def wrongTerminal : Data babyBearModulus :=
  { trace with terminalMemory :=
    [regToken 1 4 65532 64, regToken 2 5 1234 5678, ramToken 0 65 6 99 5678] }

theorem fabricated_terminal_value_rejected : ¬ Accepted wrongTerminal := by
  intro accepted
  have mismatch : ¬ (wrongTerminal.initialMemory ++ wrongTerminal.rows.flatMap Row.writes).Perm
      (wrongTerminal.terminalMemory ++ wrongTerminal.rows.flatMap Row.reads) := by decide
  exact mismatch accepted.memory

namespace Load

-- LW x1,4(x1): the native destination aliases rs1, and its prior timestamp
-- must refer to the first port's refresh. The public RAM word initially is zero.
private def loadAssignment : Nat → ZMod babyBearModulus
  | 0 | 17 | 29 => 65532
  | 2 | 8 | 27 => 4
  | 13 => 8
  | 4 | 5 | 7 | 12 | 25 | 33 | 36 | 44 | 46 | 47 | 48 => 1
  | 18 | 30 => 64
  | 20 => 65
  | 38 => 4259840
  | _ => 0

private def loadRow : Row babyBearModulus := ⟨.wordMemory, loadAssignment⟩
private def loadCells : List Cell := [.register 1, .ram 4259840]
private def loadInitial : List (MemoryToken babyBearModulus) :=
  [regToken 1 0 65532 64, ramToken 0 65 0 0 0]
private def loadTrace : Data babyBearModulus where
  rows := [loadRow]
  rom := ROM.table loadCells loadInitial
  initial := loadRow.start
  terminal := loadRow.finish
  initialMemory := loadInitial
  terminalMemory := [regToken 1 6 0 0, ramToken 0 65 5 0 0]

theorem satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment loadAssignment) (WordMemory.clockConstraints loadTrace.rom) := by
  simp [WordMemory.clockConstraints, WordMemory.importedConstraints,
    WordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, loadAssignment, Lookup.Contains, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, loadAssignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, loadAssignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (change ∃ i : Fin 1, _
       exact ⟨0, rfl⟩)

theorem accepted : Accepted loadTrace := by
  constructor
  · intro actual member
    simp only [loadTrace, List.mem_singleton] at member
    subst actual
    exact satisfies
  · intro actual member
    simp only [loadTrace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [loadTrace, loadInitial]
    decide

private theorem loadBoundary : ClockBoundary loadTrace := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro token member
    simp [loadTrace, loadInitial] at member
    rcases member with rfl | rfl <;> constructor <;> decide

private theorem loadAligned : ∀ cell ∈ loadCells, cell.Aligned := by
  intro cell member
  simp [loadCells] at member
  rcases member with rfl | rfl <;> trivial

end Load
end Tests.TraceStore
