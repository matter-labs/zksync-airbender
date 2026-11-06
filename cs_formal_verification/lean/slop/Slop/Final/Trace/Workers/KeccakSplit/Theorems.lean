import Human.Trace.Workers.KeccakSplit.Theorems
import Slop.KeccakSplit.Contract
import Slop.KeccakSplit.Setup.Control
import Slop.KeccakSplit.Chain.Calls
import Slop.KeccakSplit.Field

namespace Airbender.Keccak.Split.Native
open Proofs

/-- In an initialized pool of split Keccak workers, every access executes in Sail and
    every row is a call of the documented schedule: it reads that call's control,
    writes the next one, and writes the call's parity / theta+rho / chi result on its
    lanes. No read, range, pointer or result premise is supplied. -/
theorem operation_execution [Fact p.Prime] (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : MemoryAccepted data) (inputs : OperationInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    MemoryExecution data before cells ∧ ∀ row ∈ data.rows, RowEffects row := by
  obtain rfl := scale256_field inverse
  exact Proofs.operation_execution row_contract Split.Proofs.control_facts accepted inputs aligned

/-- A complete initialized split request: its 361 calls execute, in schedule order,
    one documented call each (`Call.ExecutesAt`) on actual Sail states, and together
    write Clean's original Keccak-f[1600] permutation of the state block at the public
    x11 pointer. Matching derives the call order, controls, pointer, reads and ranges. -/
theorem permutation_soundness [Fact p.Prime] (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : MemoryAccepted data) (inputs : CallInputs data initial cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (states : Fin 362 → Reference.RiscV.Sail.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      states 0 = initial ∧ (∀ index : Fin 361, Call.ExecutesAt index (states index.castSucc) (states index.succ)) ∧
      Keccak.Permutation.WordMapping initial (states 361) pointer input output ∧
      TraceMapping data initial (states 361) cells ∧ output = Specs.Keccak256.keccakPermutation input := by
  obtain rfl := scale256_field inverse
  obtain ⟨states, pointer, start, executes, pointerRead, laneReads, trace⟩ :=
    call_chain row_contract Split.Proofs.control_facts accepted inputs aligned
  obtain ⟨input, output, mapping, result⟩ :=
    Call.Proofs.permutation_of_executions states pointer executes pointerRead laneReads
  subst start
  exact ⟨states, pointer, input, output, rfl, executes, mapping, trace, result⟩

end Airbender.Keccak.Split.Native
