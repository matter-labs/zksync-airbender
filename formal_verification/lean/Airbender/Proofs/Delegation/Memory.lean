import Airbender.Review.Delegation.Memory
import Airbender.Proofs.Bigint.Timestamp
import Airbender.Proofs.Blake2G.Timestamp
import Airbender.Proofs.Blake2Round.Timestamp
import Airbender.Proofs.Keccak.Timestamp
import Airbender.Proofs.Trace.MemoryPaths
import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.Trace.OfflineMemory
import Airbender.Proofs.Trace.Addresses

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

theorem writes_bounded [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports) :
    (timeOfPair (row.writeToken port).time).Bounded ∧
      (timeOfPair (row.writeToken port).time).value =
        (decodeTimestamp row.assignment row.columns.invocation).value + port.clock.offset := by
  have facts := row_facts data.setup row (accepted.constraints row member)
  exact Trace.Proofs.write_time hp (base := rawPair row.assignment row.columns.invocation) facts.invocation (inputs.aligned row member)
    (facts.offsets port.clock (clock_member row present))

private theorem produced_bounded [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, (timeOfPair token.time).Bounded := by
  intro token member
  rcases List.mem_append.mp member with initial | written
  · exact Trace.Proofs.image_clocks inputs.initialization token initial
  · obtain ⟨edge, step, rfl⟩ := List.mem_map.mp written
    obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp step
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    exact (writes_bounded hp accepted inputs rowMember (by simpa using present)).1

theorem memory_clocks [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    ∀ edge ∈ data.steps,
      (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  intro edge member
  constructor
  · apply produced_bounded hp accepted inputs
    apply accepted.matching.mem_iff.mpr
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩))
  · exact produced_bounded hp accepted inputs edge.2
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))

theorem memory_order [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    ∀ edge ∈ data.steps, (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value := by
  intro edge member
  have previous := (memory_clocks (by omega) accepted inputs edge member).1
  obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
  have inArray : port ∈ row.ports := by simpa using present
  have facts := row_facts data.setup row (accepted.constraints row rowMember)
  have native := facts.comparisons port.clock (clock_member row inArray)
  have less := Trace.Proofs.native_port_order hp facts.invocation previous
    (facts.offsets port.clock (clock_member row inArray)) (inputs.aligned row rowMember)
    native.1 (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using native.2.1)
    (by simpa [decodeTimestamp, timeOfPair, readToken, rawPair] using native.2.2)
  exact less.trans_eq (writes_bounded (by omega) accepted inputs rowMember inArray).2.symm

theorem preserved_addresses {data : MemoryData p} :
    ∀ edge ∈ data.steps, edge.1.address = edge.2.address := by
  intro edge member
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp step
  rfl

theorem address_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports) :
    (port.address.word row.assignment).Bounded := by
  have step : (readToken row.assignment port, row.writeToken port) ∈ data.steps :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩
  have initialized := Trace.Proofs.keyed_origins MemoryToken.address
    (fun token => (timeOfPair token.time).value) accepted.matching preserved_addresses
    (memory_order hp accepted inputs) _ step
  rw [Trace.Proofs.image_addresses inputs.initialization] at initialized
  obtain ⟨cell, _, same⟩ := List.mem_map.mp initialized
  rw [Trace.Proofs.address_word same.symm]
  exact Trace.Proofs.cell_address_bound cell

theorem memory_effects [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    MemoryEffects data := by
  have ordered := memory_order hp accepted inputs
  refine ⟨memory_clocks (by omega) accepted inputs, ordered, ?_⟩
  have unique : (data.initial.map MemoryToken.address).Nodup := by
    rw [Trace.Proofs.image_addresses inputs.initialization]
    exact inputs.distinct
  intro source member
  obtain ⟨sink, sinkMember, same, path, head, last, _, permutation⟩ :=
    Trace.Proofs.keyed_paths_finite MemoryToken.address (fun token => (timeOfPair token.time).value)
      accepted.matching preserved_addresses unique ordered source member
  refine ⟨sink, sinkMember, same, path, head, last, ?_, permutation⟩
  apply Trace.Proofs.rank_ordered (fun token => (timeOfPair token.time).value) path
  intro edge edgeMember
  exact ordered edge (List.mem_of_mem_filter (permutation.mem_iff.mp edgeMember))

theorem cell_histories [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    ∀ source ∈ data.initial, ∃ history : TimestampSortedMemoryAccessList,
      history.val.Perm ((0, source.address, 0, source.value) ::
        (data.steps.filter fun edge => edge.1.address = source.address).map transferEvent) ∧
      MemoryAccessList.isConsistentOnline history.val history.property := by
  intro source member
  obtain ⟨_, _, _, path, head, _, ordered, permutation⟩ :=
    (memory_effects hp accepted inputs).paths source member
  exact Trace.Proofs.cell_history_of_path data.steps source path head ordered permutation

theorem memory_soundness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    MemorySoundness data :=
  ⟨memory_effects hp accepted inputs,
    fun _ member _ present => address_bounds hp accepted inputs member present,
    cell_histories hp accepted inputs⟩

end Airbender.Delegation.Proofs
