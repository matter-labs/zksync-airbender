module
public import Tests.TraceExecution

@[expose] public section

namespace Tests.NativeROM
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def cells : List Cell := Tests.TraceExecution.cells ++ [.ram 0]
def physical : List (MemoryToken babyBearModulus) :=
  ROMView.nativeBootImage Tests.TraceExecution.cells ++ [Cell.initialToken (.ram 0) 0x2083]

def assignment : Nat → ZMod babyBearModulus
  | 4 | 7 | 25 | 35 | 37 | 44 | 46 | 47 | 48 => 1
  | 2 | 11 => 4
  | 13 => 8
  | 31 | 40 | 41 => 0x2083
  | 36 => 65472
  | 45 => 34
  | _ => 0

def nativeRow : Row babyBearModulus := ⟨.wordMemory, assignment⟩
def terminal : List (MemoryToken babyBearModulus) :=
  [⟨(Cell.register 0).addressCode, (4, 0), Nat.pair 0 0⟩,
   ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 0x2083 0⟩] ++
  (ROMView.nativeBootImage (p := babyBearModulus) Tests.TraceExecution.cells).drop 2 ++
  [⟨(Cell.ram 0).addressCode, (5, 0), Nat.pair 0 0⟩]

def trace : Data babyBearModulus where
  rows := [nativeRow]
  rom := ROM.table cells physical
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 4 (8, 0)
  initialMemory := ROMView.nativeBootImage cells
  terminalMemory := terminal

theorem native_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (WordMemory.clockConstraints trace.rom) := by
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
    | (change ∃ i : Fin 2, _
       refine ⟨1, ?_⟩
       simp [ROM.rows, cells, physical, Tests.TraceExecution.cells, ROMView.nativeBootImage,
         ROM.row, Cell.initialToken, MemoryToken.word, Word.ofBitVec, RV.ROM_END, limbBase]
       with_unfolding_all rfl)

theorem native_accepted : Accepted trace := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact native_constraints
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · decide

/-- Substituting physical ROM bytes into the native seed is incorrect. -/
theorem physical_bytes_are_not_native_seed : physical ≠ trace.initialMemory := by decide

end Tests.NativeROM
