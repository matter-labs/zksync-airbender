import Airbender.Proofs.Keccak.CallPorts
import Airbender.Proofs.Delegation.Atomic
import Airbender.Proofs.Delegation.SailHistory
import Airbender.Proofs.Keccak.CallHistory
import Airbender.Proofs.Delegation.CallState
import Mathlib.Data.List.OfFn

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem native_port_codes_distinct [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (i : Fin 649) (effects : Native.RowEffects w) (active : w Variables.execute = 1)
    (control : (w Variables.controlReadLo).val = (scheduleControl ⟨i.val, by omega⟩).packed) :
    ((Delegation.Row.mk .keccak w).memorySteps.map fun edge => edge.1.address).Nodup := by
  have shape : ((Delegation.Row.mk .keccak w).memorySteps.map fun edge => edge.1.address) =
      List.ofFn (fun port : Fin 14 => importedConstraintsMemoryPorts[port.val].address.code w) := by rfl
  rw [shape, List.nodup_iff_pairwise_ne, List.pairwise_ofFn]
  intro a b earlier same
  have equal := scheduled_ports_distinct hp i effects active control same
  subst b
  exact (Fin.lt_irrefl a) earlier

theorem native_atomic_observations [Fact p.Prime] (hp : 65536 ≤ p)
    {row : Delegation.Row p} {events : List MemoryAccess} {cells : List Cell} {before after : State}
    (i : Fin 649) (family : row.family = .keccak) (effects : Native.RowEffects row.assignment)
    (active : row.assignment Variables.execute = 1)
    (control : (row.assignment Variables.controlReadLo).val = (scheduleControl ⟨i.val, by omega⟩).packed)
    (history : SailHistory cells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
      cell.read before = .ok (memoryWord (port.readCode row.assignment)) before ∧
      cell.read after = .ok (memoryWord (port.writeCode row.assignment)) after := by
  have native : (row.memorySteps.map fun edge => edge.1.address).Nodup := by
    cases row with
    | mk kind w =>
      change kind = .keccak at family
      subst kind
      exact native_port_codes_distinct hp i effects active control
  have addresses := permutation.map (fun event => event.2.1)
  have distinct : (events.map fun event => event.2.1).Nodup := by
    apply addresses.nodup_iff.mpr
    simpa only [List.map_map, Function.comp_def, transferEvent] using native
  have noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp member)
    change edge ∈ row.ports.toList.map (fun port => (readToken row.assignment port, row.writeToken port)) at present
    obtain ⟨port, portMember, rfl⟩ : ∃ port ∈ row.ports.toList,
      (readToken row.assignment port, row.writeToken port) = edge := List.mem_map.mp present
    exact port_not_zero row (by simpa only [Array.mem_toList_iff] using portMember)
  have observations := atomic_observations history aligned noZero initial distinct
  intro port member
  have present : transferEvent (readToken row.assignment port, row.writeToken port) ∈ events := by
    apply permutation.mem_iff.mpr
    apply List.mem_map.mpr
    refine ⟨(readToken row.assignment port, row.writeToken port), ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨port, by simpa only [Array.mem_toList_iff] using member, rfl⟩
  exact observations _ present

theorem call_atomic_observations [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ordered : List (Delegation.Row p)) (after : State), ordered.Perm data.rows ∧
      GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after ∧
      ∀ row ∈ ordered, ∃ events start finish, events.Perm (row.memorySteps.map transferEvent) ∧
        SailHistory cells events start finish ∧
        ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
          cell.read start = .ok (memoryWord (port.readCode row.assignment)) start ∧
          cell.read finish = .ok (memoryWord (port.writeCode row.assignment)) finish := by
  obtain ⟨ordered, after, permutation, history, _⟩ := call_history hp inverse accepted inputs tables aligned
  obtain ⟨_, schedule, _, effects⟩ := call_execution hp inverse accepted inputs tables aligned
  obtain ⟨ascending, count, perm, _, controls⟩ := schedule
  have noZero : ∀ row ∈ ordered, ∀ event ∈ row.memorySteps.map transferEvent,
      event.2.1 ≠ (Cell.register 0).addressCode := by
    intro row _ event included
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp included
    change edge ∈ row.ports.toList.map (fun port => (readToken row.assignment port, row.writeToken port)) at present
    obtain ⟨port, portMember, rfl⟩ : ∃ port ∈ row.ports.toList,
      (readToken row.assignment port, row.writeToken port) = edge := List.mem_map.mp present
    exact port_not_zero row (by simpa only [Array.mem_toList_iff] using portMember)
  have initialized : ∀ cell ∈ cells, ∃ value, cell.read initial = .ok value initial := by
    intro cell member
    obtain ⟨_, _, value, read, _⟩ := image_cell_source inputs.memory.initialization cell member
    exact ⟨value, read⟩
  have positions := grouped_positions history aligned noZero initialized
  refine ⟨ordered, after, permutation, history, ?_⟩
  intro row member
  have rowMember := permutation.mem_iff.mp member
  obtain ⟨events, start, finish, eventsPerm, current, readable⟩ := positions row member
  obtain ⟨index, indexBound, same⟩ := List.mem_iff_getElem.mp (perm.mem_iff.mpr rowMember)
  have bound : index < 649 := by omega
  have control := congrArg Arithmetic.Word.lo (controls ⟨index, bound⟩).1
  have control : (row.assignment Variables.controlReadLo).val =
      (scheduleControl ⟨index, by omega⟩).packed := by
    simpa only [same] using control
  exact ⟨events, start, finish, eventsPerm, current,
    native_atomic_observations (by omega) ⟨index, bound⟩ (inputs.family row rowMember)
      (effects row rowMember) (inputs.active row rowMember) control current eventsPerm aligned readable⟩

end Airbender.Keccak.Proofs
