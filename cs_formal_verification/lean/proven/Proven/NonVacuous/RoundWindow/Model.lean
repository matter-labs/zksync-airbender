module
public import Proven.NonVacuous.Blake2RoundSpan.Span
public import Proven.NonVacuous.HashCallers.PooledRow
public import Proven.NonVacuous.FamilyCallers.Block
public import Proven.NonVacuous.RoundCallers.Joint
public import Human.Trace.Machine.CodeWindows

@[expose] public section
namespace Airbender.NonVacuous.RoundWindow
open Trace Trace.Machine HashCallers
set_option warningAsError true

/-- The ten callers read the round control word and pointers from the span seed. -/
def initial : RV.State :=
  { Blake2RoundSpan.before with rom := FamilyCallers.rom .blakeRound 0 (fun _ => 0) }

/-- The ADD/SUB caller carries the full round CSR in its second source column. -/
def unrolledAssignment (pc clock previous : Nat) : Nat → ZMod babyBearModulus :=
  Function.update (PooledRow.assignment pc clock previous) 6 (0x7C7 : ZMod babyBearModulus)

/-- Each unrolled caller advances its PC and clock by four. -/
def unrolledRow (index : Nat) : Row babyBearModulus PooledFamily :=
  ⟨.addSub, unrolledAssignment (4 * index) (4 + 4 * index) (previousOf 0 4 index)⟩

def unrolledRows : List (Row babyBearModulus PooledFamily) := (List.range 10).map unrolledRow

def unifiedRows : List (Row babyBearModulus UnifiedFamily) :=
  FamilyCallers.Block.callerRows .blakeRound 0 4 0 10

/-- Public instruction addresses include one complete ten-round protocol. -/
def addresses : List (BitVec 32) := FamilyCallers.callerPCs 0 10

/-- A native entry retains the full CSR and the selected CPU family. -/
def entry (family : RVMachineDecoderFamily) (pc : BitVec 32) : RVMachineProgramEntry :=
  ⟨pc, FamilyCallers.callerBits .blakeRound, ⟨family, 0, 0x7C7, 0, ⟨0, 0⟩, 128, 0⟩⟩

def unrolledProgram : List RVMachineProgramEntry := addresses.map (entry (.pooled .addSub))

def unifiedProgram : List RVMachineProgramEntry := addresses.map (entry .unified)

/-- The shared cell domain contains x0 and each worker cell exactly once. -/
def keys : List Cell := .register 0 :: Blake2RoundSpan.cells

/-- CPU transfers touch only x0; worker transfers use the round span. -/
def machineSteps : List (Cell × MemoryToken babyBearModulus) :=
  (List.range 10).flatMap fun index => x0Steps (4 + 4 * index)

noncomputable def workers : WorkerPools babyBearModulus where
  standard := Blake2RoundSpan.workersFrom Blake2RoundSpan.seed 5
  split := ⟨[], [], []⟩

noncomputable def unrolledTrace : PooledTrace babyBearModulus where
  rows := unrolledRows
  rom := ⟨ROM.table keys (romImageRV initial keys), Verification.subwordTable (ROM.wordsRV initial)⟩
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 40 (44, 0)
  initialMemory := keys.map Blake2RoundSpan.seed
  terminalMemory := keys.map (runFinal (runFinal Blake2RoundSpan.seed machineSteps)
    (Blake2RoundSpan.spanSteps Blake2RoundSpan.seed 5))

noncomputable def unifiedTrace : UnifiedTrace babyBearModulus where
  rows := unifiedRows
  rom := UnifiedReduced.Setup.tableRV initial
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 40 (44, 0)
  initialMemory := keys.map Blake2RoundSpan.seed
  terminalMemory := keys.map (runFinal (runFinal Blake2RoundSpan.seed machineSteps)
    (Blake2RoundSpan.spanSteps Blake2RoundSpan.seed 5))

/-- One interval contains every round caller in the complete protocol. -/
def windows : List HashWindow := [⟨.round false, 4, 44⟩]

/-- The seed invariant has clock room for all ten worker calls. -/
theorem start : Blake2RoundSpan.Start Blake2RoundSpan.seed 5 :=
  ⟨Blake2RoundSpan.inv_mono Blake2RoundSpan.seed_inv (by decide), rfl, by decide⟩

theorem unrolled_rows_length : unrolledTrace.rows.length = 10 := rfl

theorem unified_rows_length : unifiedTrace.rows.length = 10 := rfl

theorem worker_rows_length : workers.standard.rows.length = 10 := rfl

theorem split_rows : workers.split.rows = [] := rfl

theorem windows_length : windows.length = 1 := rfl

theorem unrolled_initial_bounded : (timeOfPair unrolledTrace.initial.timestamp).Bounded := by
  change 4 < 524288 ∧ 0 < 524288
  decide

theorem unrolled_initial_aligned : (timeOfPair unrolledTrace.initial.timestamp).value % 4 = 0 := rfl

theorem unified_initial_bounded : (timeOfPair unifiedTrace.initial.timestamp).Bounded := by
  change 4 < 524288 ∧ 0 < 524288
  decide

theorem unified_initial_aligned : (timeOfPair unifiedTrace.initial.timestamp).value % 4 = 0 := rfl

end Airbender.NonVacuous.RoundWindow
