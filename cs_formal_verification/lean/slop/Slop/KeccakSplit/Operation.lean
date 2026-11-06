import Slop.KeccakSplit.Memory.History
import Slop.KeccakSplit.Interface
import Slop.Trace.TransferBounds

/- An initialized split pool executes in Sail and every row is a call of the
   schedule, given the per-row circuit contract. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem babyBear_clock : 2 * timestampBase + 4 < babyBearModulus := by
  norm_num [timestampBase, babyBearModulus]

/-- Matching transports canonical words to every read: writes are canonical once
    the reads before them are (the contract), and seeds are canonical. -/
theorem read_bounds (contract : RowContract) (control : Split.Proofs.ControlFacts babyBearModulus)
    {data : MemoryData babyBearModulus} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    ∀ edge ∈ data.steps, edge.1.word.Bounded := by
  have boundary := inputs.toBoundaryInputs
  have facts := transfer_facts babyBear_clock control accepted active boundary
  apply Transfer.read_bounds facts (before := before) (cells := cells)
    ⟨inputs.initialization, inputs.distinct⟩
  unfold Transfer.WriteRules
  intro edge member earlier
  obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
  apply contract.writes row (accepted.constraints row rowMember) (active row rowMember) _ port
    (by simpa using present)
  intro other otherPresent
  apply earlier (readToken row.assignment other, row.writeToken other)
    (List.mem_flatMap.mpr ⟨row, rowMember, List.mem_map.mpr ⟨other, by simpa using otherPresent, rfl⟩⟩)
  have portMember : port ∈ row.ports := by simpa using present
  have same := (writes_bounded (by norm_num [timestampBase, babyBearModulus]) boundary rowMember
    portMember).2
  have same' := (writes_bounded (by norm_num [timestampBase, babyBearModulus]) boundary rowMember
    otherPresent).2
  show (timeOfPair (row.writeToken other).time).value ≤ (timeOfPair (row.writeToken port).time).value
  rw [same', same, port_offset row portMember, port_offset row otherPresent]

theorem row_reads_bounded (contract : RowContract) (control : Split.Proofs.ControlFacts babyBearModulus)
    {data : MemoryData babyBearModulus} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {row : Row babyBearModulus} (member : row ∈ data.rows) :
    ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  intro port present
  exact read_bounds contract control accepted active inputs _
    (List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩)

theorem operation_execution (contract : RowContract) (control : Split.Proofs.ControlFacts babyBearModulus)
    {data : MemoryData babyBearModulus} {before : State} {cells : List Cell}
    (accepted : MemoryAccepted data) (inputs : OperationInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    MemoryExecution data before cells ∧ ∀ row ∈ data.rows, RowEffects row := by
  refine ⟨native_memory_execution babyBear_clock control accepted inputs.active
    inputs.memory.toBoundaryInputs aligned, ?_⟩
  intro row member
  exact contract.effects row (accepted.constraints row member) (inputs.active row member)
    (row_reads_bounded contract control accepted inputs.active inputs.memory member)

end Airbender.Keccak.Split.Native.Proofs
