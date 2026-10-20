import Human.Helpers.Memory.Initialization
import Slop.Trace.InitialImage

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- The profile seed is the existing actual-read image, not a second memory
    semantics. No missing runtime cell is silently supplied with a default. -/
theorem boot_image {before : State} {cells : List Cell}
    (profile : InitialProfile before cells) :
    bootImage (p := p) before cells = initialImage before cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    have tail : InitialProfile before cells :=
      ⟨profile.pc, profile.registers,
        fun address member => profile.ram address (List.mem_cons_of_mem cell member)⟩
    have checked := ih tail
    simp only [bootImage, initialImage, List.mapM_cons] at checked ⊢
    rw [checked]
    cases cell with
    | register index => rw [profile.registers index]
    | ram address =>
      by_cases rom : address.toNat < ROM.limit
      · simp only [ite_eq_left rom]
        rfl
      · simp only [ite_eq_right rom, profile.ram address List.mem_cons_self (Nat.le_of_not_gt rom)]

/-- Fixed boot PC/time and the canonical seed discharge all existing initial
    PC/clock/image premises. Per-row bounds remain derived by the trace proofs. -/
theorem boot_boundary {p : Nat} [Fact p.Prime] (hp : 4 < p)
    {before : State} {cells : List Cell} {trace : Data p}
    (profile : InitialProfile before cells)
    (image : bootImage before cells = some trace.initialMemory)
    (initial : trace.initial = PCState.boundary 0 (4, 0)) :
    initialImage before cells = some trace.initialMemory ∧
      initialState before (4, 0) = some trace.initial ∧ ClockBoundary trace := by
  have actual : initialImage before cells = some trace.initialMemory := by
    rw [← boot_image profile]
    exact image
  refine ⟨actual, ?_, ?_⟩
  · rw [initialState, profile.pc, initial]
  · refine ⟨?_, ?_, image_clocks actual⟩
    · rw [initial]
      change (4 : ZMod p).val < timestampBase ∧ (0 : ZMod p).val < timestampBase
      rw [ZMod.val_ofNat_of_lt hp]
      norm_num [timestampBase]
    · rw [initial]
      change ((4 : ZMod p).val + timestampBase * (0 : ZMod p).val) % 4 = 0
      rw [ZMod.val_ofNat_of_lt hp]
      norm_num

end Airbender.Trace.Proofs
