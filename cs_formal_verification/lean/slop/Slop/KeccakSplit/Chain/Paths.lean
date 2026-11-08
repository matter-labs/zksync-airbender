module
public import Slop.KeccakSplit.Operation
public import Slop.Delegation.CallPaths
public import Slop.Trace.MemoryPaths

@[expose] public section

/- The x10 control cell's history in a 361-call request: matching links the 361
   control accesses into one path from the public start value 0; each row's
   contract forces the next control word, so the path is the schedule's controls
   and orders the rows. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- The x10 port (port 0) of each worker. -/
def controlPort : Kind → MemoryPort
  | .columnParity => ColumnParity.importedConstraintsMemoryPorts[0]
  | .thetaRho => ThetaRho.importedConstraintsMemoryPorts[0]
  | .chi5 => Chi5.importedConstraintsMemoryPorts[0]

def controlEdge (row : Row p) : MemoryToken p × MemoryToken p :=
  (readToken row.assignment (controlPort row.kind), row.writeToken (controlPort row.kind))

theorem control_port_member (row : Row p) : controlPort row.kind ∈ row.ports := by
  cases row with
  | mk kind w => cases kind <;> exact Array.getElem_mem _

theorem control_words (row : Row p) :
    row.readWord 0 = (controlEdge row).1.word ∧ row.writtenWord 0 = (controlEdge row).2.word := by
  cases row with
  | mk kind w => cases kind <;> exact ⟨rfl, rfl⟩

/-- Only port 0 addresses x10. -/
theorem row_control_steps (row : Row p) :
    row.memorySteps.filter (fun edge => edge.1.address = (Cell.register 10).addressCode) =
      [controlEdge row] := by
  cases row with
  | mk kind w =>
    cases kind <;>
      simp [Row.memorySteps, Row.ports, controlEdge, controlPort, readToken,
        ColumnParity.importedConstraintsMemoryPorts, ThetaRho.importedConstraintsMemoryPorts,
        Chi5.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, pairCode,
        Nat.pair_eq_pair]

theorem control_edges {data : MemoryData p} :
    (data.steps.filter fun edge => edge.1.address = (Cell.register 10).addressCode) =
      data.rows.map controlEdge := by
  simp only [MemoryData.steps, List.filter_flatMap, List.map_eq_flatMap]
  change (data.rows.map _).flatten = (data.rows.map _).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row _
  exact row_control_steps row

theorem control_start : controlAt 0 = 0 := by rfl

theorem control_next : ∀ index : Fin 360, bump (controlAt index.val) = controlAt (index.val + 1) := by
  decide +kernel

theorem control_small : ∀ index : Fin 361, controlAt index.val < 65536 := by
  decide +kernel

/-- One step of the control path: the row reading control word `c` writes `bump c`. -/
def advance (word : Word) : Word := ⟨bump word.lo, 0⟩

theorem advance_iterate (n : Nat) (bound : n < 361) :
    advance^[n] ⟨0, 0⟩ = ⟨controlAt n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [advance]
    rw [control_next ⟨n, by omega⟩]

end Airbender.Keccak.Split.Native.Proofs
