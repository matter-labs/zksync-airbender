import Airbender.Review.Helpers.Memory.NativeBoot
import Airbender.Proofs.Trace.Initialization
import Airbender.Proofs.Trace.Families.WordMemory.Composition

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Verification
open _root_.Sail.ArchSem

/-- The unchanged physical Sail boot constructor is all-zero on the architectural
    domain. Actual public ROM bytes are outside this projected domain. -/
theorem architectural_boot_image {p : Nat} {before : State} {cells : List Cell}
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true) :
    bootImage (p := p) before cells = some (ROMView.nativeBootImage cells) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    have tail := ih (fun cell member => kept cell (List.mem_cons_of_mem _ member))
    simp only [bootImage, ROMView.nativeBootImage, List.mapM_cons, List.map_cons] at tail ⊢
    rw [tail]
    cases cell with
    | register index => rfl
    | ram address =>
      have outside := architectural_ram_domain kept address List.mem_cons_self
      simp only [ROM.limit, if_neg (Nat.not_lt.mpr outside)]
      rfl

/-- The original initial-state profile supplies actual Sail reads of every
    architectural zero token; missing cells are not silently defaulted. -/
theorem native_boot_shadow_boundary {p : Nat} [Fact p.Prime]
    {trace : Data p WordMemoryFamily} {before : State} {cells : List Cell} {shadows : List (BitVec 32)}
    (inputs : NativeBootBoundary trace before cells shadows) :
    ShadowImageBoundary trace before cells (bootShadowSeeds shadows) := by
  have image : initialImage (p := p) before cells = some (ROMView.nativeBootImage cells) := by
    rw [← Trace.Proofs.boot_image inputs.profile]
    exact architectural_boot_image inputs.architectural
  constructor
  · simpa only [bootShadowSeeds, List.map_map, Function.comp_def] using inputs.domain
  · exact inputs.architectural
  · intro seed member
    obtain ⟨address, present, rfl⟩ := List.mem_map.mp member
    exact inputs.shadowsInROM address present
  · rw [shadowInitialImage, image, inputs.seed]
    simp only [Option.map_some, ROMView.nativeBootImage, List.map_append, shadowTokens,
      bootShadowSeeds, List.map_map, Function.comp_def]
  · rw [initialState, inputs.profile.pc, inputs.initial]

/-- Fixed native boot data now feeds the checked initialized execution theorem.
    Accepted history derives all row reads/ranges/states and exact terminal cells. -/
theorem native_boot_execution_soundness [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup}
    {initial : State} {cells : List Cell} {shadows : List (BitVec 32)} {count logCapacity romCount : Nat}
    (inputs : NativeBootBoundary trace initial cells shadows)
    (decoder : decoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (configuration : FlatMemoryConfiguration initial)
    (image : wordROMImage initial romCount = some trace.rom) (programROM : count ≤ 1048576)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (covered : ∀ address ∈ shadows, address.toNat < 4 * romCount) :
    WordMemory.Realizes setup.program trace initial cells := by
  apply image_execution_soundness (native_boot_shadow_boundary inputs) decoder accepted decoded
    aligned configuration image programROM ordinary
  intro seed member
  obtain ⟨address, present, rfl⟩ := List.mem_map.mp member
  exact covered address present

end Airbender.WordMemory.Proofs
