import Airbender.Review.Helpers.Memory.ShadowImage
import Airbender.Proofs.Trace.Projection
import Airbender.Proofs.Trace.Families.WordMemory.ZeroRegister

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace

@[simp] theorem architectural_register (index : BitVec 5) :
    architecturalAddress (Cell.register index).addressCode = true := by
  simp [architecturalAddress, shadow, Cell.addressCode, Nat.unpair_pair]

@[simp] theorem architectural_ram (address : BitVec 32) :
    architecturalAddress (Cell.ram address).addressCode = decide (4194304 ≤ address.toNat) := by
  have region : (Word.ofBitVec address).hi < 64 ↔ address.toNat < 4194304 := by
    simp only [Word.ofBitVec, limbBase]
    omega
  by_cases inside : address.toNat < 4194304
  · simp [architecturalAddress, shadow, Cell.addressCode, Nat.unpair_pair,
      region.mpr inside, Nat.not_le.mpr inside]
  · simp [architecturalAddress, shadow, Cell.addressCode, Nat.unpair_pair,
      mt region.mp inside, Nat.le_of_not_gt inside]

theorem shadow_image_parts {p : Nat} [Fact p.Prime]
    {trace : Data p WordMemoryFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} (inputs : ShadowImageBoundary trace before cells seeds) :
    ∃ tokens, initialImage before cells = some tokens ∧
      trace.initialMemory = tokens ++ shadowTokens seeds := by
  cases image : initialImage (p := p) before cells with
  | none =>
    have impossible := inputs.image
    simp [shadowInitialImage, image] at impossible
  | some tokens =>
    exact ⟨tokens, rfl, by simpa [shadowInitialImage, image] using inputs.image.symm⟩

/-- Native seed clocks/uniqueness follow from the public constructors, including
    erased shadow seeds; no architectural read of a shadow address is needed. -/
theorem shadow_image_unique {p : Nat} [Fact p.Prime]
    {trace : Data p WordMemoryFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} (inputs : ShadowImageBoundary trace before cells seeds) :
    (trace.initialMemory.map MemoryToken.address).Nodup := by
  obtain ⟨tokens, image, combined⟩ := shadow_image_parts inputs
  rw [combined, List.map_append, Trace.Proofs.image_addresses image]
  have domain := inputs.domain.map Trace.Proofs.cell_address_injective
  simpa only [List.map_append, List.map_map, Function.comp_def, shadowTokens,
    Cell.initialToken] using domain

theorem shadow_clock_boundary {p : Nat} [Fact p.Prime] (hp : 4 < p)
    {trace : Data p WordMemoryFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} (inputs : ShadowImageBoundary trace before cells seeds) :
    ClockBoundary trace := by
  have four : (4 : ZMod p).val = 4 := ZMod.val_natCast_of_lt hp
  obtain ⟨pc, _, initial⟩ := Trace.Proofs.initial_state_source inputs.initial
  obtain ⟨tokens, image, combined⟩ := shadow_image_parts inputs
  constructor
  · rw [initial]
    change (timeOfPair ((4 : ZMod p), 0)).Bounded
    simp [timeOfPair, Timestamp.Bounded, four, timestampBase]
  · rw [initial]
    change (timeOfPair ((4 : ZMod p), 0)).value % 4 = 0
    simp [timeOfPair, Timestamp.value, four]
  · intro token present
    rw [combined] at present
    rcases List.mem_append.mp present with real | ghost
    · exact Trace.Proofs.image_clocks image token real
    · obtain ⟨seed, _, rfl⟩ := List.mem_map.mp ghost
      simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]

/-- Filtering the native seeds recovers precisely the actual Sail image of the
    architectural cells, regardless of native shadow values or missing ROM bytes. -/
theorem shadow_image_projection {p : Nat} [Fact p.Prime]
    {trace : Data p WordMemoryFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} (inputs : ShadowImageBoundary trace before cells seeds) :
    initialImage before cells =
      some (trace.initialMemory.filter fun token => architecturalAddress token.address) := by
  obtain ⟨tokens, image, combined⟩ := shadow_image_parts inputs
  have real : tokens.filter (fun token => architecturalAddress token.address) = tokens := by
    apply List.filter_eq_self.mpr
    intro token present
    obtain ⟨cell, member, _, _, rfl⟩ := Trace.Proofs.image_sources image token present
    exact inputs.architectural cell member
  have ghost : (shadowTokens (p := p) seeds).filter
      (fun token => architecturalAddress token.address) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro token present
    obtain ⟨seed, member, rfl⟩ := List.mem_map.mp present
    simpa only [Cell.initialToken, architectural_ram, decide_eq_true_eq, not_le] using
      inputs.shadows seed member
  rw [combined, List.filter_append, real, ghost, List.append_nil]
  exact image

/-- Both constructor branches contain canonical RV32 words. Native shadow
    bounds require no corresponding Sail memory read. -/
theorem shadow_image_bounds {p : Nat} [Fact p.Prime]
    {trace : Data p WordMemoryFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} (inputs : ShadowImageBoundary trace before cells seeds) :
    ∀ token ∈ trace.initialMemory, token.word.Bounded := by
  obtain ⟨tokens, image, combined⟩ := shadow_image_parts inputs
  intro token present
  rw [combined] at present
  rcases List.mem_append.mp present with real | ghost
  · exact Trace.Proofs.image_bounds image token real
  · obtain ⟨seed, _, rfl⟩ := List.mem_map.mp ghost
    rw [Trace.Proofs.initial_token_word]
    exact Word.ofBitVec_bound _

/-- The existing full-native decreasing-time range induction is unchanged.
    It retains discarded shadow reads even though Sail transfers project them out. -/
theorem shadow_value_bounds {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have clocks := shadow_clock_boundary (by omega) inputs
  have bounds := shadow_image_bounds inputs
  have rules := decoded_write_rules hp accepted decoded
  exact ⟨Trace.Proofs.read_bounds_of_rules clockSize accepted clocks bounds rules,
    Trace.Proofs.write_bounds_of_rules clockSize accepted clocks bounds rules,
    Trace.Proofs.terminal_bounds_of_rules clockSize accepted clocks bounds rules⟩

/-- Only the architectural GPR seed can have x0's address. Ghost native RAM
    values are independent of Sail ROM bytes and cannot enter this induction. -/
theorem shadow_initial_zero {p : Nat} [Fact p.Prime]
    {trace : Data p WordMemoryFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} (inputs : ShadowImageBoundary trace before cells seeds)
    {token : MemoryToken p} (present : token ∈ trace.initialMemory)
    (address : token.address = (Cell.register 0).addressCode) : token.value = 0 := by
  obtain ⟨tokens, image, combined⟩ := shadow_image_parts inputs
  rw [combined] at present
  rcases List.mem_append.mp present with real | ghost
  · obtain ⟨cell, _, value, read, rfl⟩ := Trace.Proofs.image_sources image token real
    have same := Trace.Proofs.cell_address_injective address
    subst cell
    change EStateM.Result.ok (0 : BitVec 32) before = .ok value before at read
    have zero := (EStateM.Result.ok.inj read).1.symm
    subst value
    rfl
  · obtain ⟨seed, _, rfl⟩ := List.mem_map.mp ghost
    simp [Cell.initialToken, Cell.addressCode, Nat.pair_eq_pair] at address

/-- Every retained native access is rooted in an architectural seed. The erased
    native seeds and accesses still participate in accepted memory matching. -/
theorem shadow_event_cells {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} (inputs : ShadowImageBoundary trace before cells seeds)
    (accepted : Accepted trace) :
    ∀ event ∈ trace.nativeEvents, architecturalAddress event.2.1 = true →
      ∃ cell ∈ cells, cell.addressCode = event.2.1 := by
  intro event member selected
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value, edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp rowEdge
  have origin := Trace.Proofs.initialized_addresses (by dsimp [timestampBase]; omega)
    accepted (shadow_clock_boundary (by omega) inputs) row rowMember port (by simpa using portMember)
  obtain ⟨token, present, address⟩ := List.mem_map.mp origin
  have retained : token ∈ trace.initialMemory.filter
      (fun source => architecturalAddress source.address) :=
    List.mem_filter.mpr ⟨present, by rw [address]; exact selected⟩
  obtain ⟨cell, cellMember, _, _, same⟩ :=
    Trace.Proofs.image_sources (shadow_image_projection inputs) token retained
  exact ⟨cell, cellMember, by rw [same] at address; exact address⟩

/-- Derive the native x0 write law using the unchanged decreasing-time proof,
    with the actual architectural seed constructor providing its root. -/
theorem shadow_zero_writes {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} {setup : DecoderSetup}
    (inputs : ShadowImageBoundary trace before cells seeds) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 := by
  have preserves := decoded_zero_preserving hp accepted decoded
  have reads := Trace.Proofs.zero_reads_from_seeds (by dsimp [timestampBase]; omega)
    accepted (shadow_clock_boundary (by omega) inputs)
    (fun _ present address => shadow_initial_zero inputs present address) preserves
  exact Trace.Proofs.zero_writes_from_reads reads preserves

/-- Derive row order from full native clocks, then realize only architectural
    accesses. Final architectural cells still match the complete native history. -/
theorem projected_row_history {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p WordMemoryFamily))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells
        ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) before after ∧
      SailStateMatches cells history after := by
  have boundary := shadow_clock_boundary (by omega) inputs
  obtain ⟨history, events, after, checked, permutation, sorted, actual, final⟩ :=
    Trace.Proofs.projected_native_sail_history (by dsimp [timestampBase]; omega)
      accepted boundary (shadow_image_unique inputs) architecturalAddress
      (shadow_image_projection inputs) (List.nodup_append.mp inputs.domain).1 aligned
      inputs.architectural (shadow_event_cells hp inputs accepted)
      (shadow_zero_writes hp inputs accepted decoded)
  obtain ⟨rows, rowPermutation, ordered, groupedSorted, grouped⟩ :=
    Trace.Proofs.native_row_order (by dsimp [timestampBase]; omega) accepted boundary
  have same := List.Perm.eq_of_pairwise' groupedSorted sorted (grouped.trans permutation.symm)
  exact ⟨history, rows, after, checked, rowPermutation, ordered, same.symm ▸ actual, final⟩

end Airbender.WordMemory.Proofs
