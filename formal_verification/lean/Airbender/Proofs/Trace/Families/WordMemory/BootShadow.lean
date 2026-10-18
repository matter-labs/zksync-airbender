import Airbender.Proofs.Trace.Families.WordMemory.Boot
import Airbender.Proofs.WordMemory.Shadow

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Verification

/-- Every complete native memory edge at a ROM-shadow address preserves its raw
    value. The actual imported row/port is recovered from the full native graph. -/
theorem shadow_edge_value {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} (accepted : Accepted trace)
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ trace.memorySteps)
    {address : BitVec 32} (region : address.toNat < 4194304)
    (same : edge.1.address = (Cell.ram address).addressCode) : edge.1.value = edge.2.value := by
  obtain ⟨row, present, member⟩ := List.mem_flatMap.mp member
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
  cases row with
  | mk family w =>
    cases family
    change port ∈ importedConstraintsMemoryPorts.toList at portMember
    exact (shadow_refresh hp (accepted.constraints _ present) (by simpa using portMember) region same).symm

/-- Equality along each actual adjacent edge determines both path endpoints. -/
theorem path_value_preserved {α β : Type} (value : α → β) {path : List α} {first last : α}
    (head : path.head? = some first) (finish : path.getLast? = some last)
    (edges : ∀ edge ∈ path.zip path.tail, value edge.1 = value edge.2) : value first = value last := by
  induction path generalizing first with
  | nil => simp at head
  | cons item rest ih =>
    have same : item = first := by simpa using head
    subst first
    cases rest with
    | nil =>
      have same : item = last := by simpa using finish
      subst last
      rfl
    | cons next rest =>
      have firstEdge := edges (item, next) (by simp)
      exact firstEdge.trans (ih rfl (by simpa using finish) (by
        intro edge member
        apply edges edge
        simpa only [List.tail_cons, List.zip_cons_cons] using
          List.mem_cons_of_mem (item, next) member))

/-- Fixed native zero initialization and every retained native shadow refresh
    force the terminal shadow value to zero, independently of physical ROM bytes. -/
theorem native_boot_shadow_terminal {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {initial : State} {cells : List Cell} {shadows : List (BitVec 32)}
    (inputs : NativeBootBoundary trace initial cells shadows) (accepted : Accepted trace)
    {sink : MemoryToken p} (member : sink ∈ trace.terminalMemory)
    {address : BitVec 32} (region : address.toNat < 4194304)
    (same : sink.address = (Cell.ram address).addressCode) : sink.value = 0 := by
  have boundary := native_boot_shadow_boundary inputs
  have clocks := shadow_clock_boundary (by omega) boundary
  have unique := shadow_image_unique boundary
  have keys := Trace.Proofs.boundary_keys MemoryToken.address
    (Trace.Proofs.memory_steps_matched accepted) Trace.Proofs.memory_steps_address
  have terminalUnique := keys.nodup_iff.mp unique
  obtain ⟨source, present, addressCode⟩ := List.mem_map.mp
    (keys.mem_iff.mpr (List.mem_map.mpr ⟨sink, member, rfl⟩))
  obtain ⟨path, head, ⟨last, lastMember, finish, sourceAddress⟩, _, permutation⟩ :=
    Trace.Proofs.native_memory_paths (by dsimp [timestampBase]; omega) accepted clocks unique source present
  have equal := List.inj_on_of_nodup_map terminalUnique lastMember member
    (sourceAddress.trans addressCode)
  subst last
  have value := path_value_preserved MemoryToken.value head finish (by
    intro edge edgeMember
    have actual := List.mem_filter.mp (permutation.mem_iff.mp edgeMember)
    exact shadow_edge_value hp accepted actual.1 region
      ((of_decide_eq_true actual.2).trans (addressCode.trans same)))
  have zero : source.value = 0 := by
    rw [inputs.seed] at present
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp present
    rfl
  exact value.symm.trans zero

end Airbender.WordMemory.Proofs
