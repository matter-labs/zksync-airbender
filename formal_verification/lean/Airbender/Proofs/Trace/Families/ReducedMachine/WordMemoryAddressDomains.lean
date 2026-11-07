import Airbender.Proofs.ReducedMachine.NativeWordMemoryDomains
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryCodeHistory

namespace Airbender.ReducedMachine.NativeWordMemoryHistoryProofs
open Native NativeShadow NativeShadowProofs Arithmetic Trace Verification Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The actual LW shadow port or SW destination roots the effective memory
    address in real architectural seeds or independent public shadow seeds. -/
theorem effective_public_cell {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    Cell.ram (wordMemoryAddressWord row.assignment).toBitVec ∈ cells ∨
      ∃ seed ∈ seeds, seed.1 = (wordMemoryAddressWord row.assignment).toBitVec := by
  obtain ⟨entry,_,source,query,_⟩ := NativeWordMemoryDecoderProofs.trace_decoding image accepted decoded row present
  have port : ∃ port ∈ row.ports,
      port.address.code row.assignment = (Cell.ram (wordMemoryAddressWord row.assignment).toBitVec).addressCode := by
    cases row with
    | mk family w =>
      cases family
      have actual := NativeWordMemoryPortProofs.addresses (accepted.constraints _ present) source.fields query
      cases mode : entry.data.family
      · refine ⟨importedConstraintsMemoryPorts[1],by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts],?_⟩
        simpa [wordMemoryPortCells,mode] using actual 1
      · refine ⟨importedConstraintsMemoryPorts[2],by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts],?_⟩
        simpa [wordMemoryPortCells,mode] using actual 2
  obtain ⟨port,member,target⟩ := port
  have origin := Trace.Proofs.initialized_addresses (by decide)
    accepted (shadow_clock_boundary (by decide) inputs) row present port member
  obtain ⟨token,tokenMember,address⟩ := List.mem_map.mp origin
  obtain ⟨tokens,seedImage,combined⟩ := shadow_image_parts inputs
  rw [combined] at tokenMember
  rcases List.mem_append.mp tokenMember with real | ghost
  · obtain ⟨cell,cellMember,_,_,same⟩ := Trace.Proofs.image_sources seedImage token real
    rw [same] at address
    have equal := Trace.Proofs.cell_address_injective (address.trans target)
    exact Or.inl (equal ▸ cellMember)
  · obtain ⟨seed,seedMember,rfl⟩ := List.mem_map.mp ghost
    change (Cell.ram seed.1).addressCode = port.address.code row.assignment at address
    have equal := Trace.Proofs.cell_address_injective (address.trans target)
    have same : seed.1 = (wordMemoryAddressWord row.assignment).toBitVec := by
      simpa only [Cell.ram.injEq] using equal
    exact Or.inr ⟨seed,seedMember,same⟩

/-- Canonical native bounds and the public seed domains discharge address
    origins, without any per-row expected address or shadow value. -/
theorem initialized_address_domains {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    (64 ≤ (wordMemoryAddressWord row.assignment).hi →
      Cell.ram (wordMemoryAddressWord row.assignment).toBitVec ∈ cells) ∧
    ((wordMemoryAddressWord row.assignment).hi < 64 →
      ∃ seed ∈ seeds, seed.1 = (wordMemoryAddressWord row.assignment).toBitVec) := by
  have origin := effective_public_cell image inputs accepted decoded row present
  cases row with
  | mk family w =>
    cases family
    have bounds := NativeWordMemoryNumericalProofs.address_bounds (accepted.constraints _ present)
    have canonical := Word.toBitVec_toNat bounds
    rcases origin with real | ⟨seed,member,same⟩
    · have lower := architectural_ram_domain inputs.architectural _ real
      rw [canonical] at lower
      refine ⟨fun _ => real,?_⟩
      intro inside
      have low := bounds.1
      dsimp [Word.value,limbBase] at *
      omega
    · have upper := inputs.shadows seed member
      rw [same,canonical] at upper
      refine ⟨?_,fun _ => ⟨seed,member,same⟩⟩
      intro ram
      dsimp [Word.value,limbBase] at *
      omega

end Airbender.ReducedMachine.NativeWordMemoryHistoryProofs
