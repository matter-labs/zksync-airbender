import Airbender.Proofs.Reduced.SeedClocks
import Airbender.Proofs.Trace.ROMView

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Arithmetic Trace.Proofs Delegation.Caller
set_option warningAsError true

/-- Strict native matching identifies a seed address without seed value assumptions. -/
theorem native_initialized_cell [Fact p.Prime] {data : RequestTrace p}
    (facts : Transfer.Facts (mixedData data)) {cells : List Cell}
    (seed : data.machine.initialMemory = ROMView.nativeBootImage cells)
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ data.mixedSteps) :
    ∃ cell ∈ cells, cell.addressCode = edge.1.address := by
  have origin := Trace.Proofs.keyed_origins MemoryToken.address
    (fun token => (timeOfPair token.time).value) facts.matching facts.addresses facts.order edge member
  change edge.1.address ∈ data.machine.initialMemory.map MemoryToken.address at origin
  rw [seed] at origin
  simp only [ROMView.nativeBootImage, List.map_map, Cell.initialToken] at origin
  exact List.mem_map.mp origin

/-- Every ordinary native port has the canonical address of an initialized cell. -/
theorem native_ordinary_addresses [Fact p.Prime] {data : RequestTrace p}
    (facts : Transfer.Facts (mixedData data)) {cells : List Cell}
    (seed : data.machine.initialMemory = ROMView.nativeBootImage cells)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    (ordinary : row ∉ data.callers) :
    ∀ port ∈ row.ports, (port.address.word row.assignment).Bounded := by
  intro port present
  have included : port ∈ machinePorts row := by
    rwa [machine_ports_ordinary member ordinary]
  obtain ⟨cell, _, equal⟩ := native_initialized_cell facts seed (mixed_machine_member member included)
  rw [Trace.Proofs.address_word equal.symm]
  exact Trace.Proofs.cell_address_bound cell

end Airbender.AddSub.Modular.External.Caller.Proofs
