import Airbender.Review.Helpers.Memory.ReducedMachineShadowImage
import Airbender.Proofs.Trace.InitialImage

namespace Airbender.ReducedMachine.NativeShadowProofs
open Arithmetic Trace NativeShadow
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

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
    {trace : Data p NativeReducedFamily} {before : Reference.RiscV.Sail.State}
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
    {trace : Data p NativeReducedFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} (inputs : ShadowImageBoundary trace before cells seeds) :
    (trace.initialMemory.map MemoryToken.address).Nodup := by
  obtain ⟨tokens, image, combined⟩ := shadow_image_parts inputs
  rw [combined, List.map_append, Trace.Proofs.image_addresses image]
  have domain := inputs.domain.map Trace.Proofs.cell_address_injective
  simpa only [List.map_append, List.map_map, Function.comp_def, shadowTokens,
    Cell.initialToken] using domain

theorem shadow_clock_boundary {p : Nat} [Fact p.Prime] (hp : 4 < p)
    {trace : Data p NativeReducedFamily} {before : Reference.RiscV.Sail.State}
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
    {trace : Data p NativeReducedFamily} {before : Reference.RiscV.Sail.State}
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
    {trace : Data p NativeReducedFamily} {before : Reference.RiscV.Sail.State}
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

/-- Public constructor facts only: actual seed image/projection, uniqueness,
    clock boundary and all seed ranges. No native read or Sail ROM value is assumed. -/
theorem seed_initialization {p : Nat} [Fact p.Prime] (hp : 4 < p)
    {trace : Data p NativeReducedFamily} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) :
    initialImage before cells = some (trace.initialMemory.filter fun token => architecturalAddress token.address) ∧
      (trace.initialMemory.map MemoryToken.address).Nodup ∧ ClockBoundary trace ∧
      (∀ token ∈ trace.initialMemory, token.word.Bounded) :=
  ⟨shadow_image_projection inputs,shadow_image_unique inputs,shadow_clock_boundary hp inputs,shadow_image_bounds inputs⟩

end Airbender.ReducedMachine.NativeShadowProofs
