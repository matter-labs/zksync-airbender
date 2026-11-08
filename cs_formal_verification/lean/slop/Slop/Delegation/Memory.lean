import Human.Helpers.Delegation.Memory
import Slop.Bigint.Timestamp
import Slop.Blake2G.Timestamp
import Slop.Blake2Round.Timestamp
import Slop.Keccak.Timestamp
import Slop.Trace.MemoryPaths
import Slop.Trace.InitialImage
import Slop.Trace.OfflineMemory
import Slop.Trace.Addresses
import Slop.Delegation.BoundaryInputs

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384

theorem row_facts [Fact p.Prime] (setup : Setup p) (row : Row p)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup)) : ClockFacts row.columns row.assignment := by
  cases row with
  | mk family w =>
    cases family with
    | bigint => exact Bigint.Proofs.clock_facts h
    | blakeG => exact Blake2G.Proofs.clock_facts h
    | blakeRound => exact Blake2Round.Proofs.clock_facts h
    | keccak => exact Keccak.Proofs.clock_facts h

theorem ports_clocks (row : Row p) : row.ports.map MemoryPort.clock = row.columns.ports := by
  cases row with
  | mk family w =>
    cases family with
    | bigint => exact Bigint.memory_clocks
    | blakeG => exact Blake2G.memory_clocks
    | blakeRound => exact Blake2Round.memory_clocks
    | keccak => exact Keccak.memory_clocks

theorem clock_member (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    port.clock ∈ row.columns.ports := by
  rw [← ports_clocks row]
  exact Array.mem_map.mpr ⟨port, member, rfl⟩

theorem port_offset (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    port.clock.offset = 2 := by
  have shape : row.ports.map (fun port => port.clock.offset) = Array.replicate row.ports.size 2 := by
    cases row with
    | mk family w =>
      cases family
      all_goals simp [Row.ports, Bigint.importedConstraintsMemoryPorts,
        Blake2G.importedConstraintsMemoryPorts, Blake2Round.importedConstraintsMemoryPorts,
        Keccak.importedConstraintsMemoryPorts]
      all_goals decide
  have mapped : port.clock.offset ∈ row.ports.map (fun port => port.clock.offset) :=
    Array.mem_map.mpr ⟨port, member, rfl⟩
  rw [shape] at mapped
  exact (Array.mem_replicate.mp mapped).2

theorem preserved_addresses {data : MemoryData p} :
    ∀ edge ∈ data.steps, edge.1.address = edge.2.address := by
  intro edge member
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp step
  rfl

end Airbender.Delegation.Proofs
