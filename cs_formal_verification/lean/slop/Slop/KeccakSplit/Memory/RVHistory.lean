import Human.Trace.Workers.KeccakSplit.RVExecution
import Slop.KeccakSplit.Memory.History
import Slop.KeccakSplit.Operation
import Slop.Trace.RVTransfer
import Slop.Trace.RVHistoryFrame
import Slop.Trace.SeedTransfer
import Slop.Trace.TransferBounds

/-! RV twins of the split pool's memory layer (`Memory/History.lean`, `Operation.lean`): state-free seed facts
    (`SeedInputs`: the seed domain, canonical seed words and clocks, the clock room), the RV boundary (seed facts plus
    each seed token's RV read), the RV history of all accesses and the RV memory execution. RAM cells are RAM at any
    address, the shadow RAM below `ROM_END` included. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- State-free public seed facts of a split pool. -/
structure SeedInputs (data : MemoryData p) (cells : List Cell) : Prop
    extends SeedTransfer.SeedInputs (transferData data) cells where
  words : ∀ token ∈ data.initial, token.word.Bounded
  clocks : ∀ token ∈ data.initial, (timeOfPair token.time).Bounded
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase
  invocationHigh : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase

theorem SeedInputs.invocation {data : MemoryData p} {cells : List Cell}
    (inputs : SeedInputs data cells) {row : Row p} (member : row ∈ data.rows) :
    (decodeTimestamp row.assignment row.columns.invocation).Bounded :=
  ⟨by have := inputs.clockRoom row member; omega, inputs.invocationHigh row member⟩

theorem seed_writes_bounded [Fact p.Prime] (hp : timestampBase < p)
    {data : MemoryData p} {cells : List Cell} (inputs : SeedInputs data cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports) :
    (timeOfPair (row.writeToken port).time).Bounded ∧
      (timeOfPair (row.writeToken port).time).value =
        (decodeTimestamp row.assignment row.columns.invocation).value + port.clock.offset := by
  apply Trace.Proofs.write_time_of_room hp (base := rawPair row.assignment row.columns.invocation)
    (inputs.invocation member)
  rw [port_offset row present]
  exact inputs.clockRoom row member

theorem seed_memory_order [Fact p.Prime] (hp : 2 * timestampBase + 4 < p) (control : Split.Proofs.ControlFacts p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {cells : List Cell} (inputs : SeedInputs data cells) :
    ∀ edge ∈ data.steps, (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value := by
  have produced : ∀ token ∈ data.initial ++ data.steps.map Prod.snd, (timeOfPair token.time).Bounded := by
    intro token member
    rcases List.mem_append.mp member with initial | written
    · exact inputs.clocks token initial
    · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp written
      obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp present
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
      exact (seed_writes_bounded (by omega) inputs rowMember (by simpa using portMember)).1
  intro edge member
  have previous : (timeOfPair edge.1.time).Bounded := by
    apply produced
    apply accepted.matching.mem_iff.mpr
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩))
  obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
  have inArray : port ∈ row.ports := by simpa using present
  have room : (decodeTimestamp row.assignment row.columns.invocation).lo + port.clock.offset <
      timestampBase := by
    rw [port_offset row inArray]
    exact inputs.clockRoom row rowMember
  have less := Split.Proofs.split_physical_port_order hp control row
    (accepted.constraints row rowMember) (active row rowMember) inArray
    (inputs.invocation rowMember) previous room
  exact less.trans_eq (seed_writes_bounded (by omega) inputs rowMember inArray).2.symm

theorem seed_transfer_facts [Fact p.Prime] (hp : 2 * timestampBase + 4 < p) (control : Split.Proofs.ControlFacts p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {cells : List Cell} (inputs : SeedInputs data cells) :
    Transfer.Facts (transferData data) :=
  ⟨accepted.matching, preserved_addresses, seed_memory_order hp control accepted active inputs⟩

/-- RV sibling of `BoundaryInputs`: the seed facts and each seed token's RV read. -/
structure RVBoundaryInputs (data : MemoryData p) (before : RV.State) (cells : List Cell) : Prop
    extends toSeed : SeedInputs data cells where
  reads : ∀ token ∈ data.initial, ∃ cell ∈ cells, cell.addressCode = token.address ∧
    cell.readRV before = some (memoryWord token.value)

theorem RVBoundaryInputs.transfer {data : MemoryData p} {before : RV.State} {cells : List Cell}
    (inputs : RVBoundaryInputs data before cells) :
    Transfer.RVBoundaryInputs (transferData data) before cells :=
  ⟨inputs.toSeed.toSeedInputs, inputs.reads⟩

private theorem rv_image_sources {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens) :
    ∀ token ∈ tokens, ∃ cell ∈ cells, ∃ value,
      cell.readRV before = some value ∧ token = cell.initialToken value := by
  have reads := rvImage_reads cells tokens image
  clear image
  induction reads with
  | nil => simp
  | @cons cell token cells tokens head tail ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨value, read, same⟩ := head
      exact ⟨cell, List.mem_cons_self, value, read, same⟩
    · obtain ⟨source, sourceMember, value, read, same⟩ := ih actual member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, value, read, same⟩

theorem _root_.Airbender.Keccak.Split.Native.RVMemoryInputs.toRVBoundaryInputs {data : MemoryData p} {before : RV.State} {cells : List Cell}
    (inputs : RVMemoryInputs data before cells) : RVBoundaryInputs data before cells := by
  have sources := rv_image_sources inputs.initialization
  refine ⟨⟨⟨?_, inputs.distinct⟩, ?_, ?_, inputs.clockRoom, inputs.invocationHigh⟩, ?_⟩
  · change (data.initial.map MemoryToken.address).Perm (cells.map Cell.addressCode)
    rw [rvImage_addresses inputs.initialization]
  · intro token member
    obtain ⟨cell, _, value, _, rfl⟩ := sources token member
    rw [initial_token_word]
    exact Word.ofBitVec_bound value
  · intro token member
    obtain ⟨cell, _, value, _, rfl⟩ := sources token member
    simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]
  · intro token member
    obtain ⟨cell, present, value, read, rfl⟩ := sources token member
    refine ⟨cell, present, rfl, ?_⟩
    simp only [Cell.initialToken, memoryWord, Nat.unpair_pair]
    rw [Word.ofBitVec_roundtrip]
    exact read

theorem rv_native_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (control : Split.Proofs.ControlFacts p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before : RV.State} {cells : List Cell} (inputs : RVBoundaryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess) (after : RV.State),
      history.val.Perm (Transfer.labeledEvents (transferData data)) ∧
      events.Perm (data.steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧
      RVHistory cells events before after ∧ RVStateMatches cells history after := by
  apply Transfer.rv_native_history_at_boundary
    (seed_transfer_facts hp control accepted active inputs.toSeed) inputs.transfer aligned
  intro edge present same
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
  exact False.elim (port_not_zero row (by simpa using portMember) same)

theorem rv_native_memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (control : Split.Proofs.ControlFacts p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {before : RV.State} {cells : List Cell} (inputs : RVBoundaryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    RVMemoryExecution data before cells := by
  obtain ⟨history, events, after, bound, permutation, order, actual, final⟩ :=
    rv_native_history hp control accepted active inputs aligned
  refine ⟨events, after, permutation, order, actual, ?_, ?_,
    Transfer.rv_terminal_reads_at_boundary (seed_transfer_facts hp control accepted active inputs.toSeed)
      inputs.transfer bound final⟩
  · intro edge member
    have access := rv_history_access_execution actual
      (permutation.mem_iff.mpr (List.mem_map.mpr ⟨edge, member, rfl⟩))
    simpa [Delegation.RVPortExecution, Trace.transferEvent, Trace.memoryWord, Trace.MemoryToken.word] using access
  · intro cell cellAligned untouched value read
    apply rv_history_cell_frame actual aligned cell cellAligned _ read
    intro event member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp member)
    exact untouched edge present

/-- Seed twin of `Operation.read_bounds`: matching transports canonical words to every read. -/
theorem seed_read_bounds (contract : RowContract) (control : Split.Proofs.ControlFacts babyBearModulus)
    {data : MemoryData babyBearModulus} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {cells : List Cell} (inputs : SeedInputs data cells) :
    ∀ edge ∈ data.steps, edge.1.word.Bounded := by
  have facts := seed_transfer_facts babyBear_clock control accepted active inputs
  have produced := Transfer.produced_bounds_of_seed facts inputs.words (by
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
    have same := (seed_writes_bounded (by norm_num [timestampBase, babyBearModulus]) inputs rowMember
      portMember).2
    have same' := (seed_writes_bounded (by norm_num [timestampBase, babyBearModulus]) inputs rowMember
      otherPresent).2
    show (timeOfPair (row.writeToken other).time).value ≤ (timeOfPair (row.writeToken port).time).value
    rw [same', same, port_offset row portMember, port_offset row otherPresent])
  intro edge present
  exact produced edge.1 (facts.matching.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩))))

theorem seed_row_reads_bounded (contract : RowContract) (control : Split.Proofs.ControlFacts babyBearModulus)
    {data : MemoryData babyBearModulus} (accepted : MemoryAccepted data)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    {cells : List Cell} (inputs : SeedInputs data cells)
    {row : Row babyBearModulus} (member : row ∈ data.rows) :
    ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  intro port present
  exact seed_read_bounds contract control accepted active inputs _
    (List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩)

/-- RV twin of `Operation.operation_execution`. -/
theorem rv_operation_execution (contract : RowContract) (control : Split.Proofs.ControlFacts babyBearModulus)
    {data : MemoryData babyBearModulus} {before : RV.State} {cells : List Cell}
    (accepted : MemoryAccepted data) (inputs : RVOperationInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    RVMemoryExecution data before cells ∧ ∀ row ∈ data.rows, RowEffects row := by
  have boundary := inputs.memory.toRVBoundaryInputs
  refine ⟨rv_native_memory_execution babyBear_clock control accepted inputs.active boundary aligned, ?_⟩
  intro row member
  exact contract.effects row (accepted.constraints row member) (inputs.active row member)
    (seed_row_reads_bounded contract control accepted inputs.active boundary.toSeed member)

end Airbender.Keccak.Split.Native.Proofs
