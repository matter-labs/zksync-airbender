import Airbender.Proofs.UnifiedReduced.StreamInitialization
import Airbender.Review.Helpers.UnifiedReduced.StreamROMProfile

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384

/-- Public caller PCs retain the aligned text positions of their Sail bytes. -/
theorem text_caller_code {Family : Type}
    (fields : SailRV32.instruction → Option (DecoderData Family))
    (text : List (BitVec 32)) (size : text.length ≤ ROM.limit / 4) :
    ∀ entry ∈ FullUnsigned.entriesWith fields text,
      entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0 := by
  intro entry member
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  have found : text[index]? = some bits := List.mk_mem_zipIdx_iff_getElem?.mp inText
  have indexBound : index < text.length := by
    by_contra notBound
    have : text[index]? = none := by simp [Nat.le_of_not_gt notBound]
    rw [this] at found
    contradiction
  have pcBound : 4 * index < ROM.limit := by omega
  unfold FullUnsigned.entriesWith at member
  cases decoded : SailRV32.Functions.encdec_backwards bits with
  | impure call continuation => simp [decoded] at selected
  | pure instruction =>
    cases metadata : fields instruction with
    | none => simp [decoded, metadata] at selected
    | some data =>
      simp only [decoded, metadata, bind, Option.bind] at selected
      cases selected
      have wordBound : 4 * index < 2 ^ 32 := Nat.lt_trans pcBound (by decide +kernel)
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound, Nat.mul_mod_right]
        using And.intro pcBound (Nat.mul_mod_right 4 index)

/-- The target's public conditions provide the ROM-aware execution profile. -/
theorem unified_rom_profile [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    [Fact babyBearModulus.Prime]
    {initial : State} {text : List (BitVec 32)}
    {bundles : List UnifiedReduced.Caller.DelegationUse.Bundle}
    {data : UnifiedReduced.Caller.RequestTrace babyBearModulus}
    (geometry : Initialization.Geometry Initialization.unified.layout)
    (windows : Initialization.Windows Initialization.unified.layout)
    (profile : PublicProfile initial (Initialization.cells geometry windows))
    (size : text.length ≤ ROM.limit / 4)
    (registry : data.program = (unifiedProgram initial text bundles).callers)
    (loads : ∀ entry ∈ (unifiedProgram initial text bundles).ordinary,
      ∀ (imm : BitVec 12) (rs1 : BitVec 5),
      entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)) :
    UnifiedReduced.Caller.Stream.ROMProfile data
      (unifiedProgram initial text bundles).ordinary initial
      (Initialization.cells geometry windows) := by
  refine ⟨unified_program_code initial text size, ?_, ?_, profile.configuration,
    profile.ordinary, fun _ => profile.landingPadDisabled, loads⟩
  · rw [registry]
    exact text_caller_code Delegation.Caller.decoderFields text size
  · intro index
    change Cell.register index ∈ ExternalBoundary.Initialization.registers ++ _
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨⟨index.toNat, index.isLt⟩, List.mem_finRange _, ?_⟩
    simp

end Airbender.Compiler.MachineTargets.Proofs
