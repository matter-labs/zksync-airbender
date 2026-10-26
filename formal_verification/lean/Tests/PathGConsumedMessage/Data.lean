import Tests.PathGLoopNative

namespace Tests.PathGConsumedMessage
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail

set_option warningAsError true
set_option Elab.async false

/-- The same 56-call public program, with the last ordinary store targeting
message word eight, which the following G actually consumes. -/
noncomputable def before : State :=
  wordWriteState (PathGLoopProgram.before .protectedMessage) 152 0x0225a023

def storeEntry : UnifiedReduced.ProgramEntry :=
  ⟨152, 0x0225a023, .STORE (32, .Regidx 2, .Regidx 11, 4),
    ⟨.machine, 11, 2, 0, ⟨32, 0⟩, 262144, 0⟩⟩

def ordinaryProgram : List UnifiedReduced.ProgramEntry :=
  (PathGLoopProgram.ordinaryProgram .protectedMessage).map fun entry =>
    if entry.pc = 152 then storeEntry else entry

/-- Only the SW immediate, effective address and destination predecessor change. -/
def cpuStoreAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 8 then 32
  else if column = 44 ∨ column = 57 then 96
  else if column = 46 then 719
  else if column = 78 then 24
  else PathGLoopNative.machineAssignment .protectedMessage 226 column

def cpuAssignment (index : Fin 228) : Nat → ZMod babyBearModulus :=
  if index.val = 226 then cpuStoreAssignment
  else PathGLoopNative.machineAssignment .protectedMessage index

/-- Actual native chunks for G(0,0,0,0;7,0). All twelve addition carries stay
zero. The message read now follows the ordinary store at timestamp 910. -/
def finalWorkerAssignment (column : Nat) : ZMod babyBearModulus :=
  match column with
  | 17 | 69 | 71 => 119
  | 21 => 3598
  | 22 => 57582
  | 25 | 29 => 1792
  | 26 => 30471
  | 30 => 30464
  | 33 | 41 | 44 | 53 | 62 | 73 | 78 | 81 => 7
  | 79 => 112
  | 80 => 14
  | 82 => 238
  | 101 => 910
  | _ => PathGLoopNative.workerAssignment .protectedMessage 55 column

def workerAssignment (index : Fin 56) : Nat → ZMod babyBearModulus :=
  if index.val = 55 then finalWorkerAssignment
  else PathGLoopNative.workerAssignment .protectedMessage index

theorem cpu_unchanged (index : Fin 228) (different : index.val ≠ 226) :
    cpuAssignment index = PathGLoopNative.machineAssignment .protectedMessage index := by
  simp only [cpuAssignment, if_neg different]

theorem worker_unchanged (index : Fin 56) (different : index.val ≠ 55) :
    workerAssignment index = PathGLoopNative.workerAssignment .protectedMessage index := by
  simp only [workerAssignment, if_neg different]

end Tests.PathGConsumedMessage
