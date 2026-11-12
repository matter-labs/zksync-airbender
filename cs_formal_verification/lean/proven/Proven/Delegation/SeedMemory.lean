module
public import Proven.Delegation.Values
public import Proven.Trace.SeedTransfer

@[expose] public section

/-! State-free twins of the delegation memory chain (`Memory.lean` through `memory_soundness`, `History.transfer_facts`,
    `Values.lean`). Those take a Sail `BoundaryInputs` but read only its public seed facts (address domain, seed
    word and clock bounds, invocation room); here those facts are `SeedInputs`, with no machine state, so the RV
    claims (`RVExecution.lean`, `Final/Trace/Delegation/RVTheorems.lean`) can use them. Proof bodies are the Sail
    ones verbatim. -/

namespace Airbender.Delegation.SeedProofs
open Trace Arithmetic
open Airbender.Delegation.Proofs (transferData row_facts clock_member port_offset preserved_addresses WriteBoundsFromReads
  transfer_write_rules)
set_option warningAsError true
set_option maxRecDepth 16384

/-- The public seed facts of a delegation pool: the seed address domain, canonical seed words and clocks, and the
    invocation-timestamp room (`MemoryInputs.clockRoom`, `MemoryInputs.invocationHigh`). -/
structure SeedInputs (data : MemoryData p) (cells : List Cell) : Prop
    extends Trace.Proofs.SeedTransfer.SeedInputs (transferData data) cells where
  words : ∀ token ∈ data.initial, token.word.Bounded
  clocks : ∀ token ∈ data.initial, (timeOfPair token.time).Bounded
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase
  invocationHigh : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase

theorem SeedInputs.invocation {data : MemoryData p} {cells : List Cell}
    (inputs : SeedInputs data cells) {row : Row p} (member : row ∈ data.rows) :
    (decodeTimestamp row.assignment row.columns.invocation).Bounded := by
  have room := inputs.clockRoom row member
  exact ⟨by omega, inputs.invocationHigh row member⟩

theorem writes_bounded [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} (_accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports) :
    (timeOfPair (row.writeToken port).time).Bounded ∧
      (timeOfPair (row.writeToken port).time).value =
        (decodeTimestamp row.assignment row.columns.invocation).value + port.clock.offset := by
  apply Trace.Proofs.write_time_of_room hp (base := rawPair row.assignment row.columns.invocation)
    (inputs.invocation member)
  rw [port_offset row present]
  exact inputs.clockRoom row member

private theorem produced_bounded [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, (timeOfPair token.time).Bounded := by
  intro token member
  rcases List.mem_append.mp member with initial | written
  · exact inputs.clocks token initial
  · obtain ⟨edge, step, rfl⟩ := List.mem_map.mp written
    obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp step
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    exact (writes_bounded hp accepted inputs rowMember (by simpa using present)).1

theorem memory_clocks [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells) :
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
    {cells : List Cell} (inputs : SeedInputs data cells) :
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

theorem address_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells)
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

theorem memory_effects [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells) :
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

theorem cell_histories [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells) :
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
    {cells : List Cell} (inputs : SeedInputs data cells) :
    MemorySoundness data :=
  ⟨memory_effects hp accepted inputs,
    fun _ member _ present => address_bounds hp accepted inputs member present,
    cell_histories hp accepted inputs⟩

theorem transfer_facts [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells) :
    Trace.Proofs.Transfer.Facts (transferData data) :=
  ⟨accepted.matching, preserved_addresses, memory_order hp accepted inputs⟩

theorem produced_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    (rules : WriteBoundsFromReads data) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, token.word.Bounded :=
  Trace.Proofs.Transfer.produced_bounds_of_seed (transfer_facts hp accepted inputs) inputs.words
    (transfer_write_rules rules)

theorem read_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    (rules : WriteBoundsFromReads data) {row : Row p} (member : row ∈ data.rows)
    {port : MemoryPort} (present : port ∈ row.ports) : (readToken row.assignment port).word.Bounded := by
  apply produced_value_bounds hp accepted inputs rules
  apply accepted.matching.mem_iff.mpr
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_,
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩, rfl⟩))

theorem write_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    (rules : WriteBoundsFromReads data) {row : Row p} (member : row ∈ data.rows)
    {port : MemoryPort} (present : port ∈ row.ports) : (row.writeToken port).word.Bounded := by
  apply produced_value_bounds hp accepted inputs rules
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_,
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩, rfl⟩))

theorem terminal_value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    (rules : WriteBoundsFromReads data) {token : MemoryToken p} (member : token ∈ data.terminal) :
    token.word.Bounded :=
  produced_value_bounds hp accepted inputs rules token
    (accepted.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl member)))

end Airbender.Delegation.SeedProofs
