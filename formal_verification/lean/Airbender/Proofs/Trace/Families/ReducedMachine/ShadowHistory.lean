import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowImage
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryZeroRegister
import Airbender.Proofs.Trace.Projection
import Airbender.Proofs.Trace.RowHistory

namespace Airbender.ReducedMachine.NativeShadowHistoryProofs
open Native NativeShadow NativeShadowProofs Arithmetic Trace Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Only the architectural GPR seed can have x0's address. Ghost native RAM
    values are independent of Sail ROM bytes and cannot enter this induction. -/
theorem shadow_initial_zero {p : Nat} [Fact p.Prime]
    {trace : Data p NativeReducedFamily} {before : Reference.RiscV.Sail.State}
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
    {trace : Data p NativeReducedFamily} {before : Reference.RiscV.Sail.State}
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

/-- Actual native LW/SW zero preservation is rooted in the architectural x0
    seed, while every independent shadow seed remains fully matched. -/
theorem shadow_zero_writes {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) before cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup) :
    ∀ event ∈ (fixedData trace).nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 := by
  have preserves := NativeWordMemoryHistoryProofs.decoded_zero_preserving image accepted decoded
  have reads := Trace.Proofs.zero_reads_from_seeds (by decide)
    accepted (shadow_clock_boundary (by decide) inputs)
    (fun _ present address => shadow_initial_zero inputs present address) preserves
  exact Trace.Proofs.zero_writes_from_reads reads preserves

/-- Full native matching derives chronology and every projected Sail state.
    Only whole ROM-shadow addresses are filtered from Sail transfers; full
    native history/seed/read/write matching and clocks remain unchanged. -/
theorem projected_row_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) before cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus NativeReducedFamily)) (after : Reference.RiscV.Sail.State),
      MemoryHistory (fixedData trace) history ∧ rows.Perm (fixedData trace).rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells
        ((rows.flatMap fun row => (rowEvents (fixedData trace).memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) before after ∧
      SailStateMatches cells history after := by
  have boundary := shadow_clock_boundary (by decide) inputs
  obtain ⟨history,events,after,checked,permutation,sorted,actual,final⟩ :=
    Trace.Proofs.projected_native_sail_history (by decide)
      accepted boundary (shadow_image_unique inputs) architecturalAddress
      (shadow_image_projection inputs) (List.nodup_append.mp inputs.domain).1 aligned
      inputs.architectural (shadow_event_cells (by decide) inputs accepted)
      (shadow_zero_writes image inputs accepted decoded)
  obtain ⟨rows,rowPermutation,ordered,groupedSorted,grouped⟩ :=
    Trace.Proofs.native_row_order (by decide) accepted boundary
  have same := List.Perm.eq_of_pairwise' groupedSorted sorted (grouped.trans permutation.symm)
  exact ⟨history,rows,after,checked,rowPermutation,ordered,same.symm ▸ actual,final⟩

end Airbender.ReducedMachine.NativeShadowHistoryProofs
