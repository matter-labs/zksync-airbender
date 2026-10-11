import Airbender.Proofs.Delegation.History
import Airbender.Proofs.Trace.TransferBounds
import Airbender.Proofs.Trace.Values

namespace Airbender.Delegation.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

def WriteBoundsFromReads (data : MemoryData p) : Prop :=
  ∀ row ∈ data.rows, (∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) →
    ∀ port ∈ row.ports, (row.writeToken port).word.Bounded

theorem produced_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (rules : WriteBoundsFromReads data) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, token.word.Bounded := by
  apply Trace.Proofs.Transfer.produced_bounds (transfer_facts hp accepted inputs) (transferInputs inputs)
  intro edge edgeMember earlier
  obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
  have portMember : port ∈ row.ports := by simpa using present
  apply rules row rowMember ?_ port portMember
  intro source sourceMember
  have included : (readToken row.assignment source, row.writeToken source) ∈ data.steps :=
    List.mem_flatMap.mpr ⟨row, rowMember,
      List.mem_map.mpr ⟨source, by simpa using sourceMember, rfl⟩⟩
  apply earlier _ included
  have sameTime : (row.writeToken source).time = (row.writeToken port).time := by
    simp only [Row.writeToken, port_offset row sourceMember, port_offset row portMember]
  rw [sameTime]

theorem read_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (rules : WriteBoundsFromReads data) {row : Row p} (member : row ∈ data.rows)
    {port : MemoryPort} (present : port ∈ row.ports) : (readToken row.assignment port).word.Bounded := by
  apply produced_value_bounds hp accepted inputs rules
  apply accepted.matching.mem_iff.mpr
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_,
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩, rfl⟩))

theorem write_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (rules : WriteBoundsFromReads data) {row : Row p} (member : row ∈ data.rows)
    {port : MemoryPort} (present : port ∈ row.ports) : (row.writeToken port).word.Bounded := by
  apply produced_value_bounds hp accepted inputs rules
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_,
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩, rfl⟩))

theorem terminal_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (rules : WriteBoundsFromReads data) {token : MemoryToken p} (member : token ∈ data.terminal) :
    token.word.Bounded :=
  produced_value_bounds hp accepted inputs rules token
    (accepted.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl member)))

end Airbender.Delegation.Proofs
