import Airbender.Proofs.Trace.Families.WordMemory.MemoryTransport
import Airbender.Proofs.Trace.Families.WordMemory.CodeHistory

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
open _root_.Sail.ArchSem

/-- The native four-MiB ROM region lies below both actual platform MMIO windows.
    Its ordinary-address condition follows from native ranged address limbs. -/
theorem native_rom_ordinary {p : Nat} [Fact p.Prime] {rom : WordROM} {w : Nat → ZMod p}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (region : (addressWord w).hi < 64) : OrdinaryWordAddress (addressWord w).toBitVec := by
  have bounded := address_bounds native
  rw [OrdinaryWordAddress, Word.toBitVec_toNat bounded]
  change ((addressWord w).value < 33554432 ∨ 33603584 ≤ (addressWord w).value) ∧
    ((addressWord w).value < 201326592 ∨ 201326624 ≤ (addressWord w).value)
  dsimp [addressWord, Word.value] at *
  constructor <;> left <;> dsimp [limbBase] <;> omega

/-- Retained source reads and actual public ROM bytes discharge original Sail
    virtual memory. No Sail shadow read or expected ROM value is supplied. -/
theorem projected_virtual_rom_read {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 4194304 < p) {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (address : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec)
    {entry : ProgramEntry WordMemoryFamily}
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    {before after : State} (configuration : FlatMemoryConfiguration before)
    {count : Nat} (image : wordROMImage before count = some rom)
    (region : (addressWord w).hi < 64) (within : (addressWord w).value < 4 * count)
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.vmem_read (.Regidx entry.data.rs1) (immediateWord w).toBitVec 4
      (.Load .Data) false false false) before =
      .ok (.Ok (Word.mk (w 26).val (w 27).val).toBitVec) before := by
  have read := native_rom_read hp image native region within
  have aligned := effective_alignment hp native
  have ordinary := native_rom_ordinary native region
  rw [address] at read aligned ordinary
  exact virtual_word_read configuration _ _ (projected_source_read hp epoch native history query)
    aligned ordinary read

/-- Initial public construction and actual native prefixes discharge the local
    ROM transport interfaces. Prefix states and source reads are realized Sail
    transfers; no numerical, expected-read or table-equivalence premise is added. -/
theorem initialized_virtual_rom_read [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup}
    {initial before after : State} {cells : List Cell} {seeds : List ShadowSeed}
    {wordCount logCapacity romCount : Nat}
    (inputs : ShadowImageBoundary trace initial cells seeds)
    (decoder : decoderSetupImage initial wordCount logCapacity = some setup)
    (image : wordROMImage initial romCount = some trace.rom)
    (configuration : FlatMemoryConfiguration initial)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod mersenne31Modulus}
    (member : (⟨.wordMemory, w⟩ : Row mersenne31Modulus WordMemoryFamily) ∈ trace.rows)
    {events : List MemoryAccess} (past : SailHistory cells events initial before)
    (history : SailHistory cells
      ((rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row mersenne31Modulus WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after)
    (region : (addressWord w).hi < 64) (within : (addressWord w).value < 4 * romCount) :
    ∃ entry ∈ setup.program,
      (⟨.wordMemory, w⟩ : Row mersenne31Modulus WordMemoryFamily).decoderQuery = entry.query ∧
      run (SailRV32.Functions.vmem_read (.Regidx entry.data.rs1) (immediateWord w).toBitVec 4
        (.Load .Data) false false false) before =
        .ok (.Ok (Word.mk (w 26).val (w 27).val).toBitVec) before := by
  have native := accepted.constraints _ member
  obtain ⟨entry, present, query⟩ := decoder_member (by decide) native (decoded _ member)
  have address := (projected_native_effects inputs decoder accepted decoded _ member).1
  have preserved := rom_image_after_frame (projected_history_rom_bytes inputs.architectural past) image
  refine ⟨entry, present, query, ?_⟩
  exact projected_virtual_rom_read (by decide) _ native address query
    (Trace.Proofs.sail_history_configuration past configuration) preserved region within history

end Airbender.WordMemory.Proofs
