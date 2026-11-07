import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Delegation.Memory
import Airbender.Proofs.Bigint.Timestamp
import Airbender.Proofs.Blake2G.Timestamp
import Airbender.Proofs.Blake2Round.Timestamp
import Airbender.Proofs.Keccak.Timestamp
import Airbender.Proofs.Trace.MemoryPaths
import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.Trace.OfflineMemory
import Airbender.Proofs.Trace.Addresses
import Airbender.Proofs.Delegation.BoundaryInputs

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

theorem clock_room_of_invocation_slots [Fact p.Prime]
    {data : MemoryData p} (_accepted : MemoryAccepted data)
    (invocations : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).Bounded)
    (slots : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).lo % 4 = 1) :
    ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase := by
  intro row member
  have bound := (invocations row member).1
  have slot := slots row member
  dsimp [timestampBase] at bound ⊢
  omega

theorem writes_bounded [Fact p.Prime] (hp : FieldCapacity.NoWrap p timestampBase)
    {data : MemoryData p} (_accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports) :
    (timeOfPair (row.writeToken port).time).Bounded ∧
      (timeOfPair (row.writeToken port).time).value =
        (decodeTimestamp row.assignment row.columns.invocation).value + port.clock.offset := by
  apply Trace.Proofs.write_time_of_room hp (base := rawPair row.assignment row.columns.invocation)
    (inputs.invocation member)
  rw [port_offset row present]
  exact inputs.clockRoom row member

private theorem produced_bounded [Fact p.Prime] (hp : FieldCapacity.NoWrap p timestampBase)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, (timeOfPair token.time).Bounded := by
  intro token member
  rcases List.mem_append.mp member with initial | written
  · exact inputs.clocks token initial
  · obtain ⟨edge, step, rfl⟩ := List.mem_map.mp written
    obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp step
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    exact (writes_bounded hp accepted inputs rowMember (by simpa using present)).1

theorem memory_clocks [Fact p.Prime] (hp : FieldCapacity.NoWrap p timestampBase)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    ∀ edge ∈ data.steps,
      (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  intro edge member
  constructor
  · apply produced_bounded hp accepted inputs
    apply accepted.matching.mem_iff.mpr
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩))
  · exact produced_bounded hp accepted inputs edge.2
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))

theorem memory_order [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    ∀ edge ∈ data.steps, (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value := by
  intro edge member
  have previous := (memory_clocks (by omega) accepted inputs edge member).1
  obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
  have inArray : port ∈ row.ports := by simpa using present
  have facts := row_facts data.setup row (accepted.constraints row rowMember)
  have native := facts.comparisons port.clock (clock_member row inArray)
  have room : (decodeTimestamp row.assignment row.columns.invocation).lo + port.clock.offset < timestampBase := by
    rw [port_offset row inArray]
    exact inputs.clockRoom row rowMember
  have less := Trace.Proofs.native_port_order_of_room hp (inputs.invocation rowMember) previous
    (facts.offsets port.clock (clock_member row inArray)) room
    native.1 (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using native.2.1)
    (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using native.2.2)
  exact less.trans_eq (writes_bounded (by omega) accepted inputs rowMember inArray).2.symm

theorem preserved_addresses {data : MemoryData p} :
    ∀ edge ∈ data.steps, edge.1.address = edge.2.address := by
  intro edge member
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp step
  rfl

theorem address_bounds [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports) :
    (port.address.word row.assignment).Bounded := by
  have step : (readToken row.assignment port, row.writeToken port) ∈ data.steps :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩
  have initialized := Trace.Proofs.keyed_origins MemoryToken.address
    (fun token => (timeOfPair token.time).value) accepted.matching preserved_addresses
    (memory_order hp accepted inputs) _ step
  have initialized := inputs.addresses.mem_iff.mp initialized
  obtain ⟨cell, _, same⟩ := List.mem_map.mp initialized
  rw [Trace.Proofs.address_word same.symm]
  exact Trace.Proofs.cell_address_bound cell

theorem memory_effects [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    MemoryEffects data := by
  have ordered := memory_order hp accepted inputs
  refine ⟨memory_clocks (by omega) accepted inputs, ordered, ?_⟩
  have unique : (data.initial.map MemoryToken.address).Nodup := by
    exact inputs.addresses.nodup_iff.mpr inputs.distinct
  intro source member
  obtain ⟨sink, sinkMember, same, path, head, last, _, permutation⟩ :=
    Trace.Proofs.keyed_paths_finite MemoryToken.address (fun token => (timeOfPair token.time).value)
      accepted.matching preserved_addresses unique ordered source member
  refine ⟨sink, sinkMember, same, path, head, last, ?_, permutation⟩
  apply Trace.Proofs.rank_ordered (fun token => (timeOfPair token.time).value) path
  intro edge edgeMember
  exact ordered edge (List.mem_of_mem_filter (permutation.mem_iff.mp edgeMember))

theorem cell_histories [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    ∀ source ∈ data.initial, ∃ history : TimestampSortedMemoryAccessList,
      history.val.Perm ((0, source.address, 0, source.value) ::
        (data.steps.filter fun edge => edge.1.address = source.address).map transferEvent) ∧
      MemoryAccessList.isConsistentOnline history.val history.property := by
  intro source member
  obtain ⟨_, _, _, path, head, _, ordered, permutation⟩ :=
    (memory_effects hp accepted inputs).paths source member
  exact Trace.Proofs.cell_history_of_path data.steps source path head ordered permutation

theorem memory_soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    MemorySoundness data :=
  ⟨memory_effects hp accepted inputs,
    fun _ member _ present => address_bounds hp accepted inputs member present,
    cell_histories hp accepted inputs⟩

end Airbender.Delegation.Proofs
