import Airbender.Proofs.WordMemory.ROMBytePadding
import Airbender.Review.Helpers.Decoder.WordMemory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail

/-- Reuse a successful pure original decoder construction after transporting
    its actual byte read. Decoder results are not supplied independently. -/
theorem program_entry_after_read_frame {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before after : State} {pc : BitVec 32} {entry : ProgramEntry Kind}
    (image : programEntryWith projection before pc = some entry)
    (frame : ∀ value, (Cell.ram pc).read before = .ok value before →
      (Cell.ram pc).read after = .ok value after) :
    programEntryWith projection after pc = some entry := by
  unfold programEntryWith at image ⊢
  cases read : (Cell.ram pc).read before with
  | error error state => simp [read, bind, Option.bind] at image
  | ok value state =>
    have same := cell_read_frame _ read
    subst state
    have later := frame value read
    simpa only [read, later] using image

/-- Actual read transport preserves a complete selected-profile program image. -/
theorem program_image_after_read_frame {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before after : State} {addresses : List (BitVec 32)} {program : List (ProgramEntry Kind)}
    (image : programImageWith projection before addresses = some program)
    (frame : ∀ address ∈ addresses, ∀ value, (Cell.ram address).read before = .ok value before →
      (Cell.ram address).read after = .ok value after) :
    programImageWith projection after addresses = some program := by
  unfold programImageWith at image ⊢
  induction addresses generalizing program with
  | nil => exact image
  | cons address addresses ih =>
    rw [List.mapM_cons] at image ⊢
    cases first : programEntryWith projection before address with
    | none => simp [first, bind, Option.bind] at image
    | some entry =>
      cases rest : addresses.mapM (programEntryWith projection before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some entries =>
        have next := program_entry_after_read_frame first (frame address List.mem_cons_self)
        have tail := ih rest (fun address member => frame address (List.mem_cons_of_mem _ member))
        simpa only [first, rest, next, tail, bind, Option.bind] using image

end Airbender.Trace.Proofs

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Verification

/-- The actual public LW/SW decoder setup survives padding when its code lies in
    the supplied prefix. Setup entries and the full minus-one tail are retained. -/
theorem padded_decoder_setup {before : State} {count words logCapacity : Nat} {setup : DecoderSetup}
    (image : decoderSetupImage before count logCapacity = some setup)
    (code : count ≤ words) (bound : words ≤ 1048576) :
    decoderSetupImage (paddedROMState before words) count logCapacity = some setup := by
  unfold decoderSetupImage at image ⊢
  split at image
  · rename_i capacity
    rw [if_pos capacity]
    cases built : programImageWith decoderFields before
        ((List.range count).map fun i => BitVec.ofNat 32 (4 * i)) with
    | none => simp [built, bind, Option.bind] at image
    | some program =>
      have later := Trace.Proofs.program_image_after_read_frame built (after := paddedROMState before words) (by
        intro address member value read
        obtain ⟨i, present, rfl⟩ := List.mem_map.mp member
        have small := List.mem_range.mp present
        apply padded_rom_word_frame bound (Or.inl ?_) read
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega)
      simpa only [built, later] using image
  · cases image

end Airbender.WordMemory.Proofs
