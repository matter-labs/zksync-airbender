import Tests.AirbenderNative
import Airbender.Proofs.UnifiedReduced.Setup

namespace Tests.AirbenderUnifiedNative
open Airbender Airbender.Trace Airbender.Arithmetic Airbender.Initialization
open Airbender.Reference Airbender.Reference.Sail Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

/-- Four actual unified rows for the same zero-GPR LUI/ADDI/SW/LW program.
The imported ports refresh at clock offsets0/1/2; previous clocks are supplied
by the preceding access to the same cell, including the two aliased x0 reads.
The first row also carries its actual inline CLINT teardown value7/time17. -/
def luiAssignment : Nat → ZMod babyBearModulus
  | 2 | 30 | 40 => 4
  | 32 => 8
  | 4 | 7 | 11 | 44 | 129 | 130 | 131 | 132 | 133 => 1
  | 9 | 51 => 512
  | 134 => 7
  | 136 => 17
  | _ => 0

def addiAssignment : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 30 | 40 => 8
  | 32 => 12
  | 4 | 11 | 129 | 130 | 131 | 132 | 133 => 1
  | 7 | 44 => 2
  | 8 | 50 => 7
  | 34 => 5
  | _ => 0

def swAssignment : Nat → ZMod babyBearModulus
  | 0 => 8
  | 2 | 30 => 12
  | 32 => 16
  | 4 | 5 | 29 | 129 | 130 | 131 | 132 | 133 => 1
  | 6 | 38 => 2
  | 34 => 6
  | 37 | 45 | 58 => 512
  | 40 => 10
  | 42 | 50 => 7
  | 80 => 33554432 * 7 * 943718400
  | 86 => 448
  | _ => 0

def lwAssignment : Nat → ZMod babyBearModulus
  | 0 | 34 => 12
  | 2 | 30 => 16
  | 32 => 20
  | 4 | 5 | 28 | 129 | 130 | 131 | 132 | 133 => 1
  | 7 | 44 => 3
  | 37 | 39 | 58 => 512
  | 40 => 14
  | 42 | 50 => 7
  | 80 => 33554432 * 7 * 943718400
  | 86 => 448
  | _ => 0

def rows : List (Row babyBearModulus UnifiedFamily) :=
  [⟨.machine, luiAssignment⟩, ⟨.machine, addiAssignment⟩,
   ⟨.machine, swAssignment⟩, ⟨.machine, lwAssignment⟩]

def program : List UnifiedReduced.ProgramEntry :=
  AirbenderProgram.program.map fun entry =>
    ⟨entry.pc, entry.bits, entry.instruction, UnifiedReduced.arithmeticFields entry.data⟩

private theorem disabled_query_contains (setup : Table (ZMod babyBearModulus) (fields 10))
    (disabled : setup.Contains #[] (Vector.replicate 10 0))
    (query : Vector (ZMod babyBearModulus) 10) (zero : query = Vector.replicate 10 0) :
    setup.Contains #[] query := by
  rw [zero]
  exact disabled

private theorem lui_polynomials_0
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat)
    (upper : i < 16) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment luiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lui_polynomials_1
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 16 ≤ i)
    (upper : i < 32) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment luiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lui_polynomials_2
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 32 ≤ i)
    (upper : i < 48) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment luiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lui_polynomials_3
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 48 ≤ i)
    (upper : i < 64) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment luiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lui_polynomials_4
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 64 ≤ i)
    (upper : i < 80) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment luiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lui_polynomials_5
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 80 ≤ i)
    (upper : i < 96) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment luiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lui_polynomials_6
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 96 ≤ i)
    (upper : i < 112) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment luiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lui_polynomials_7
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 112 ≤ i)
    (upper : i < 128) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment luiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lui_polynomials_8
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 128 ≤ i)
    (upper : i < 129) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment luiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lui_polynomials (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment luiAssignment) = 0 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i bound
  have short : i < 129 := by simpa only [UnifiedReduced.constraint_count] using bound
  by_cases selected0 : i < 16
  · exact lui_polynomials_0 setup i selected0
  by_cases selected1 : i < 32
  · exact lui_polynomials_1 setup i (by omega) selected1
  by_cases selected2 : i < 48
  · exact lui_polynomials_2 setup i (by omega) selected2
  by_cases selected3 : i < 64
  · exact lui_polynomials_3 setup i (by omega) selected3
  by_cases selected4 : i < 80
  · exact lui_polynomials_4 setup i (by omega) selected4
  by_cases selected5 : i < 96
  · exact lui_polynomials_5 setup i (by omega) selected5
  by_cases selected6 : i < 112
  · exact lui_polynomials_6 setup i (by omega) selected6
  by_cases selected7 : i < 128
  · exact lui_polynomials_7 setup i (by omega) selected7
  exact lui_polynomials_8 setup i (by omega) short

private theorem lui_lookups (setup : Table (ZMod babyBearModulus) (fields 10))
    (disabled : setup.Contains #[] (Vector.replicate 10 0)) :
    ∀ lookup ∈ FlatOperation.lookups (UnifiedReduced.importedConstraints setup),
      lookup.Contains (Verification.environment luiAssignment) := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i bound
  have short : i < 18 := by simpa only [UnifiedReduced.lookup_count] using bound
  by_cases range : i < 13
  · interval_cases i
    all_goals first
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
  · have pooled : 13 ≤ i := by omega
    interval_cases i
    all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.lookups]
    all_goals simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals dsimp only [Lookup.Contains, Table.toRaw, Verification.environment, fromElements]
    all_goals rw [Array.map_empty]
    all_goals change setup.Contains #[] _
    all_goals apply disabled_query_contains setup disabled
    all_goals decide +kernel

private theorem lui_timestamps :
    FlatOperation.ConstraintsHoldFlat (Verification.environment luiAssignment)
      UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem lui_constraints (setup : Table (ZMod babyBearModulus) (fields 10))
    (disabled : setup.Contains #[] (Vector.replicate 10 0)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment luiAssignment)
      (UnifiedReduced.clockConstraints setup) := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    exact ⟨lui_polynomials setup, lui_lookups setup disabled⟩
  · exact lui_timestamps

private theorem addi_polynomials_0
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat)
    (upper : i < 16) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment addiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem addi_polynomials_1
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 16 ≤ i)
    (upper : i < 32) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment addiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem addi_polynomials_2
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 32 ≤ i)
    (upper : i < 48) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment addiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem addi_polynomials_3
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 48 ≤ i)
    (upper : i < 64) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment addiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem addi_polynomials_4
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 64 ≤ i)
    (upper : i < 80) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment addiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem addi_polynomials_5
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 80 ≤ i)
    (upper : i < 96) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment addiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem addi_polynomials_6
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 96 ≤ i)
    (upper : i < 112) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment addiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem addi_polynomials_7
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 112 ≤ i)
    (upper : i < 128) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment addiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem addi_polynomials_8
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 128 ≤ i)
    (upper : i < 129) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment addiAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem addi_polynomials (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment addiAssignment) = 0 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i bound
  have short : i < 129 := by simpa only [UnifiedReduced.constraint_count] using bound
  by_cases selected0 : i < 16
  · exact addi_polynomials_0 setup i selected0
  by_cases selected1 : i < 32
  · exact addi_polynomials_1 setup i (by omega) selected1
  by_cases selected2 : i < 48
  · exact addi_polynomials_2 setup i (by omega) selected2
  by_cases selected3 : i < 64
  · exact addi_polynomials_3 setup i (by omega) selected3
  by_cases selected4 : i < 80
  · exact addi_polynomials_4 setup i (by omega) selected4
  by_cases selected5 : i < 96
  · exact addi_polynomials_5 setup i (by omega) selected5
  by_cases selected6 : i < 112
  · exact addi_polynomials_6 setup i (by omega) selected6
  by_cases selected7 : i < 128
  · exact addi_polynomials_7 setup i (by omega) selected7
  exact addi_polynomials_8 setup i (by omega) short

private theorem addi_lookups (setup : Table (ZMod babyBearModulus) (fields 10))
    (disabled : setup.Contains #[] (Vector.replicate 10 0)) :
    ∀ lookup ∈ FlatOperation.lookups (UnifiedReduced.importedConstraints setup),
      lookup.Contains (Verification.environment addiAssignment) := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i bound
  have short : i < 18 := by simpa only [UnifiedReduced.lookup_count] using bound
  by_cases range : i < 13
  · interval_cases i
    all_goals first
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
  · have pooled : 13 ≤ i := by omega
    interval_cases i
    all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.lookups]
    all_goals simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals dsimp only [Lookup.Contains, Table.toRaw, Verification.environment, fromElements]
    all_goals rw [Array.map_empty]
    all_goals change setup.Contains #[] _
    all_goals apply disabled_query_contains setup disabled
    all_goals decide +kernel

private theorem addi_timestamps :
    FlatOperation.ConstraintsHoldFlat (Verification.environment addiAssignment)
      UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem addi_constraints (setup : Table (ZMod babyBearModulus) (fields 10))
    (disabled : setup.Contains #[] (Vector.replicate 10 0)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment addiAssignment)
      (UnifiedReduced.clockConstraints setup) := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    exact ⟨addi_polynomials setup, addi_lookups setup disabled⟩
  · exact addi_timestamps

private theorem sw_polynomials_0
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat)
    (upper : i < 16) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment swAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem sw_polynomials_1
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 16 ≤ i)
    (upper : i < 32) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment swAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem sw_polynomials_2
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 32 ≤ i)
    (upper : i < 48) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment swAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem sw_polynomials_3
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 48 ≤ i)
    (upper : i < 64) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment swAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem sw_polynomials_4
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 64 ≤ i)
    (upper : i < 80) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment swAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem sw_polynomials_5
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 80 ≤ i)
    (upper : i < 96) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment swAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem sw_polynomials_6
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 96 ≤ i)
    (upper : i < 112) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment swAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem sw_polynomials_7
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 112 ≤ i)
    (upper : i < 128) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment swAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem sw_polynomials_8
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 128 ≤ i)
    (upper : i < 129) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment swAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem sw_polynomials (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment swAssignment) = 0 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i bound
  have short : i < 129 := by simpa only [UnifiedReduced.constraint_count] using bound
  by_cases selected0 : i < 16
  · exact sw_polynomials_0 setup i selected0
  by_cases selected1 : i < 32
  · exact sw_polynomials_1 setup i (by omega) selected1
  by_cases selected2 : i < 48
  · exact sw_polynomials_2 setup i (by omega) selected2
  by_cases selected3 : i < 64
  · exact sw_polynomials_3 setup i (by omega) selected3
  by_cases selected4 : i < 80
  · exact sw_polynomials_4 setup i (by omega) selected4
  by_cases selected5 : i < 96
  · exact sw_polynomials_5 setup i (by omega) selected5
  by_cases selected6 : i < 112
  · exact sw_polynomials_6 setup i (by omega) selected6
  by_cases selected7 : i < 128
  · exact sw_polynomials_7 setup i (by omega) selected7
  exact sw_polynomials_8 setup i (by omega) short

private theorem sw_lookups (setup : Table (ZMod babyBearModulus) (fields 10))
    (disabled : setup.Contains #[] (Vector.replicate 10 0)) :
    ∀ lookup ∈ FlatOperation.lookups (UnifiedReduced.importedConstraints setup),
      lookup.Contains (Verification.environment swAssignment) := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i bound
  have short : i < 18 := by simpa only [UnifiedReduced.lookup_count] using bound
  by_cases range : i < 13
  · interval_cases i
    all_goals first
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
  · have pooled : 13 ≤ i := by omega
    interval_cases i
    all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.lookups]
    all_goals simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals dsimp only [Lookup.Contains, Table.toRaw, Verification.environment, fromElements]
    all_goals rw [Array.map_empty]
    all_goals change setup.Contains #[] _
    all_goals apply disabled_query_contains setup disabled
    all_goals decide +kernel

private theorem sw_timestamps :
    FlatOperation.ConstraintsHoldFlat (Verification.environment swAssignment)
      UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem sw_constraints (setup : Table (ZMod babyBearModulus) (fields 10))
    (disabled : setup.Contains #[] (Vector.replicate 10 0)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment swAssignment)
      (UnifiedReduced.clockConstraints setup) := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    exact ⟨sw_polynomials setup, sw_lookups setup disabled⟩
  · exact sw_timestamps

private theorem lw_polynomials_0
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat)
    (upper : i < 16) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment lwAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lw_polynomials_1
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 16 ≤ i)
    (upper : i < 32) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment lwAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lw_polynomials_2
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 32 ≤ i)
    (upper : i < 48) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment lwAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lw_polynomials_3
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 48 ≤ i)
    (upper : i < 64) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment lwAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lw_polynomials_4
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 64 ≤ i)
    (upper : i < 80) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment lwAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lw_polynomials_5
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 80 ≤ i)
    (upper : i < 96) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment lwAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lw_polynomials_6
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 96 ≤ i)
    (upper : i < 112) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment lwAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lw_polynomials_7
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 112 ≤ i)
    (upper : i < 128) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment lwAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lw_polynomials_8
    (setup : Table (ZMod babyBearModulus) (fields 10)) (i : Nat) (lower : 128 ≤ i)
    (upper : i < 129) :
    ((FlatOperation.constraints (UnifiedReduced.importedConstraints setup))[i]'(by
      simpa only [UnifiedReduced.constraint_count] using (show i < 129 by omega))).eval
        (Verification.environment lwAssignment) = 0 := by
  interval_cases i
  all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.constraints]
  all_goals try simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals decide +kernel

private theorem lw_polynomials (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment lwAssignment) = 0 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i bound
  have short : i < 129 := by simpa only [UnifiedReduced.constraint_count] using bound
  by_cases selected0 : i < 16
  · exact lw_polynomials_0 setup i selected0
  by_cases selected1 : i < 32
  · exact lw_polynomials_1 setup i (by omega) selected1
  by_cases selected2 : i < 48
  · exact lw_polynomials_2 setup i (by omega) selected2
  by_cases selected3 : i < 64
  · exact lw_polynomials_3 setup i (by omega) selected3
  by_cases selected4 : i < 80
  · exact lw_polynomials_4 setup i (by omega) selected4
  by_cases selected5 : i < 96
  · exact lw_polynomials_5 setup i (by omega) selected5
  by_cases selected6 : i < 112
  · exact lw_polynomials_6 setup i (by omega) selected6
  by_cases selected7 : i < 128
  · exact lw_polynomials_7 setup i (by omega) selected7
  exact lw_polynomials_8 setup i (by omega) short

private theorem lw_lookups (setup : Table (ZMod babyBearModulus) (fields 10))
    (disabled : setup.Contains #[] (Vector.replicate 10 0)) :
    ∀ lookup ∈ FlatOperation.lookups (UnifiedReduced.importedConstraints setup),
      lookup.Contains (Verification.environment lwAssignment) := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i bound
  have short : i < 18 := by simpa only [UnifiedReduced.lookup_count] using bound
  by_cases range : i < 13
  · interval_cases i
    all_goals first
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
  · have pooled : 13 ≤ i := by omega
    interval_cases i
    all_goals dsimp only [UnifiedReduced.importedConstraints, FlatOperation.lookups]
    all_goals simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals dsimp only [Lookup.Contains, Table.toRaw, Verification.environment, fromElements]
    all_goals rw [Array.map_empty]
    all_goals change setup.Contains #[] _
    all_goals apply disabled_query_contains setup disabled
    all_goals decide +kernel

private theorem lw_timestamps :
    FlatOperation.ConstraintsHoldFlat (Verification.environment lwAssignment)
      UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem lw_constraints (setup : Table (ZMod babyBearModulus) (fields 10))
    (disabled : setup.Contains #[] (Vector.replicate 10 0)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment lwAssignment)
      (UnifiedReduced.clockConstraints setup) := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    exact ⟨lw_polynomials setup, lw_lookups setup disabled⟩
  · exact lw_timestamps

noncomputable def trace (domain : List Cell) : UnifiedTrace babyBearModulus where
  rows := rows
  rom := UnifiedReduced.Setup.table AirbenderProgram.before
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 16 (20, 0)
  initialMemory := domain.map AirbenderNative.old
  terminalMemory := domain.map AirbenderNative.final

private theorem disabled :
    (UnifiedReduced.Setup.table (p := babyBearModulus) AirbenderProgram.before).Contains
      #[] (Vector.replicate 10 0) := by
  change ∃ index : Fin 2097537, Vector.replicate 10 (0 : ZMod babyBearModulus) =
    (UnifiedReduced.Setup.row AirbenderProgram.before index).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨0, ?_⟩
  rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
  change Vector.replicate 10 (0 : ZMod babyBearModulus) =
    (UnifiedReduced.Setup.referenceBinaryRow 0).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  unfold UnifiedReduced.Setup.referenceBinaryRow
  rw [Verification.shiftBinopRow_eq_reference]
  decide +kernel

/-- Only five cells participate in the four instructions. Every other selected
native cell remains in the symbolic domain and cancels by the generic frame. -/
theorem accepted (domain : List Cell) (distinct : domain.Nodup)
    (subset : AirbenderNative.touched ⊆ domain) : Accepted (trace domain) := by
  constructor
  · intro row member
    change row ∈ rows at member
    simp only [rows, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact lui_constraints _ disabled
    · exact addi_constraints _ disabled
    · exact sw_constraints _ disabled
    · exact lw_constraints _ disabled
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
  · apply Trace.FiniteFootprint.balance_of_nodup domain AirbenderNative.touched
      AirbenderNative.old AirbenderNative.final (rows.flatMap Row.reads) (rows.flatMap Row.writes)
      distinct (by decide) subset
    · intro cell _ outside
      dsimp only [AirbenderNative.final]
      split_ifs
      all_goals first
        | rfl
        | (exfalso; apply outside; subst cell; decide)
    · decide

theorem decoded (domain : List Cell) : UnifiedReduced.Decoded (trace domain) program := by
  intro row member
  change row ∈ rows at member
  simp only [rows, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨⟨0, by decide⟩, by decide⟩
  · exact ⟨⟨1, by decide⟩, by decide⟩
  · exact ⟨⟨2, by decide⟩, by decide⟩
  · exact ⟨⟨3, by decide⟩, by decide⟩

/-- Reproject the already proved concrete fetch/decoding and original Sail
execution; only the native metadata registry changes. -/
theorem decoded_execution : Relation.ReflTransGen (UnifiedReduced.Step program)
    AirbenderProgram.before AirbenderProgram.afterLW := by
  apply Relation.ReflTransGen.mono _ AirbenderProgram.decoded_execution
  rintro before after ⟨entry, member, source, pc, clause, selected, execution⟩
  refine ⟨⟨entry.pc, entry.bits, entry.instruction, UnifiedReduced.arithmeticFields entry.data⟩,
    List.mem_map.mpr ⟨entry, member, rfl⟩,
    ⟨source.bytes, source.decoded, ?_⟩, pc, clause, selected, execution⟩
  simp [UnifiedReduced.decoderFields, source.fields]

/-- These observations follow from actual original execution, including the
store followed by load at the first address in the CLINT region. -/
theorem terminal :
    run (SailRV32.Functions.get_arch_pc ()) AirbenderProgram.afterLW =
      .ok 16 AirbenderProgram.afterLW ∧
    (Cell.register 3).read AirbenderProgram.afterLW = .ok 7 AirbenderProgram.afterLW ∧
    (Cell.ram 33554432).read AirbenderProgram.afterLW = .ok 7 AirbenderProgram.afterLW :=
  ⟨AirbenderProgram.terminal.1, AirbenderProgram.terminal.2.2.2.1,
    AirbenderProgram.terminal.2.2.2.2⟩

end Tests.AirbenderUnifiedNative
