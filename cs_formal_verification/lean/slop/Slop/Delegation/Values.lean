module
public import Slop.Trace.TransferBounds
public import Slop.Delegation.BoundaryInputs
public import Slop.Delegation.Memory

@[expose] public section

namespace Airbender.Delegation.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

def WriteBoundsFromReads (data : MemoryData p) : Prop :=
  ∀ row ∈ data.rows, (∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) →
    ∀ port ∈ row.ports, (row.writeToken port).word.Bounded

theorem transfer_write_rules {data : MemoryData p} (rules : WriteBoundsFromReads data) :
    Trace.Proofs.Transfer.WriteRules (transferData data) := by
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

end Airbender.Delegation.Proofs
