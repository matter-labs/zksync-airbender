import Tests.ShiftHistoryRows
import Airbender.Review.Circuits.ShiftBinop.BinaryModel

namespace Tests.ShiftHistoryFixture
open Airbender Arithmetic Trace Verification ShiftBinop Tests.ShiftHistoryRows
open Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def immediate (sample : Fin 24) : Bool := 6 ≤ sample.val % 12
def discarded (sample : Fin 24) : Bool := 12 ≤ sample.val

def before (sample : Fin 24) : State :=
  { (default : State) with regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (0x8000ffff : BitVec 32) |>.insert .x2 (3 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (BitVec.ofNat 32 (4 * sample.val))) }

def nativeRow (sample : Fin 24) : Row mersenne31Modulus ShiftBinopFamily :=
  ⟨.shiftBinop,assignment sample⟩

private def cell (register time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair register 0),(time,0),Nat.pair (value%65536) (value/65536)⟩

def trace (sample : Fin 24) : Data mersenne31Modulus ShiftBinopFamily where
  rows := [nativeRow sample]
  rom := ()
  initial := ⟨(4 * sample.val,0),(4,0)⟩
  terminal := ⟨(4 * sample.val + 4,0),(8,0)⟩
  initialMemory := [cell 0 0 0,cell 1 0 0x8000ffff,cell 2 0 3,cell 3 0 0]
  terminalMemory := [cell 0 (if discarded sample then 6 else if immediate sample then 5 else 0) 0,
    cell 1 4 0x8000ffff,cell 2 (if immediate sample then 0 else 5) 3,
    cell 3 (if discarded sample then 0 else 6) (writtenWord (assignment sample)).value]

private theorem memory_matches (sample : Fin 24) :
    ((trace sample).initialMemory ++ (trace sample).rows.flatMap Row.writes).Perm
      ((trace sample).terminalMemory ++ (trace sample).rows.flatMap Row.reads) := by
  fin_cases sample <;> decide +kernel

theorem accepted (sample : Fin 24) : Accepted (trace sample) := by
  constructor
  · intro row member
    have same : row = nativeRow sample := by simpa [trace] using member
    subst row
    exact native_constraints sample
  · intro row member
    have same : row = nativeRow sample := by simpa [trace] using member
    subst row
    fin_cases sample <;> decide
  · change [(trace sample).initial,(nativeRow sample).finish].Perm
      [(trace sample).terminal,(nativeRow sample).start]
    have start : (nativeRow sample).start = (trace sample).initial := by
      fin_cases sample <;> rfl
    have finish : (nativeRow sample).finish = (trace sample).terminal := by
      fin_cases sample <;> rfl
    rw [start,finish]
    exact List.Perm.swap _ _ []
  · exact memory_matches sample

theorem public_inputs (sample : Fin 24) :
    ImageBoundary (trace sample) (before sample)
      [.register 0,.register 1,.register 2,.register 3] := by
  have zero : (Cell.register 0).read (before sample) = .ok (0 : BitVec 32) (before sample) := rfl
  have first : (Cell.register 1).read (before sample) =
      .ok (0x8000ffff : BitVec 32) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have second : (Cell.register 2).read (before sample) = .ok (3 : BitVec 32) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have third : (Cell.register 3).read (before sample) = .ok (0 : BitVec 32) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (before sample) =
      .ok (BitVec.ofNat 32 (4 * sample.val)) (before sample) := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,first,second,third]
    rfl
  · rw [initialState,pc]
    fin_cases sample <;> rfl

/-- The old local row uses timestamp zero for both x0 reads. The second read
    must instead consume the earlier x0 read's refresh at timestamp five. -/
def staleTrace (sample : Fin 6) : Data mersenne31Modulus ShiftBinopFamily :=
  { trace ⟨18 + sample.val, by omega⟩ with
    rows := [⟨.shiftBinop,ShiftRoutingWitness.assignment ⟨18 + sample.val, by omega⟩⟩] }

theorem stale_local_constraints (sample : Fin 6) :
    ∀ row ∈ (staleTrace sample).rows,
      FlatOperation.ConstraintsHoldFlat (environment row.assignment) ShiftBinop.importedConstraints := by
  intro row member
  have same : row = ⟨.shiftBinop,ShiftRoutingWitness.assignment ⟨18 + sample.val, by omega⟩⟩ := by
    simpa [staleTrace] using member
  subst row
  exact ShiftRouting.native_constraints _

/-- All six stale immediate/x0 choices fail actual native logical matching. -/
theorem stale_rejected (sample : Fin 6) : ¬Accepted (staleTrace sample) := by
  intro h
  have count := h.memory.count_eq (cell 0 5 0)
  revert count
  fin_cases sample <;> decide +kernel

end Tests.ShiftHistoryFixture
