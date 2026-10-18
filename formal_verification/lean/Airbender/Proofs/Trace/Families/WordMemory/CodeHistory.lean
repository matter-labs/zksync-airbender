import Airbender.Proofs.Trace.Families.WordMemory.ShadowImage
import Airbender.Proofs.Trace.CodeHistory
import Airbender.Proofs.WordMemory.ROMImage

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Verification Reference.RiscV.Sail

/-- The checked architectural address predicate places actual Sail RAM cells
    above the native ROM prefix; native ghost cells remain only in matching. -/
theorem architectural_ram_domain {cells : List Cell}
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    (address : BitVec 32) (member : Cell.ram address ∈ cells) :
    4194304 ≤ address.toNat := by
  have selected := kept (Cell.ram address) member
  rw [architectural_ram] at selected
  exact of_decide_eq_true selected

/-- Every projected instruction prefix preserves every actual ROM byte, even
    when the byte is absent or its word is outside the tracked cell domain. -/
theorem projected_history_rom_bytes {cells : List Cell}
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    {events : List MemoryAccess} {before after : State}
    (history : SailHistory cells events before after) :
    ∀ key < 4194304, after.mem[key]? = before.mem[key]? :=
  Trace.Proofs.history_byte_frame_of_domain history (architectural_ram_domain kept)

/-- A public program fitting the native ROM region supplies each complete
    code-byte window. Indexed PCs are derived from actual setup construction. -/
theorem setup_rom_pc {before : State} {count logCapacity : Nat} {setup : DecoderSetup}
    (image : decoderSetupImage before count logCapacity = some setup)
    (profile : count ≤ 1048576) :
    ∀ entry ∈ setup.program, entry.pc.toNat + 4 ≤ 4194304 := by
  unfold decoderSetupImage at image
  split at image
  · cases built : programImageWith decoderFields before
        ((List.range count).map fun i => BitVec.ofNat 32 (4 * i)) with
    | none => simp [built] at image
    | some program =>
      simp only [built, bind, Option.bind, pure, Option.some.injEq] at image
      subst setup
      intro entry member
      have addresses := Trace.Proofs.program_addresses built
      have present : entry.pc ∈ (List.range count).map (fun i => BitVec.ofNat 32 (4 * i)) := by
        rw [← addresses]
        exact List.mem_map.mpr ⟨entry, member, rfl⟩
      obtain ⟨i, bound, same⟩ := List.mem_map.mp present
      have index := List.mem_range.mp bound
      rw [← same, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  · cases image

/-- Original public code reads and pure decoding survive every projected
    history prefix. No expected instruction read in the later state is assumed. -/
theorem setup_sources_after_history {cells : List Cell}
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    {events : List MemoryAccess} {before after : State}
    (history : SailHistory cells events before after)
    {count logCapacity : Nat} {setup : DecoderSetup}
    (image : decoderSetupImage before count logCapacity = some setup)
    (profile : count ≤ 1048576) :
    ∀ entry ∈ setup.program, entry.SourceWith after decoderFields := by
  intro entry present
  exact Trace.Proofs.entry_source_after_byte_frame (projected_history_rom_bytes kept history)
    (setup_sources image entry present) (setup_rom_pc image profile entry present)
    (setup_decoders_pure image entry present)

/-- Add code/ROM preservation to the existing initialized architectural-history
    assembly. All native seeds and discarded shadow accesses remain matched. -/
theorem projected_rom_preservation {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {setup : DecoderSetup} {before : State}
    {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p WordMemoryFamily)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      SailHistory cells
        ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) before after ∧
      SailStateMatches cells history after ∧
      (∀ key < 4194304, after.mem[key]? = before.mem[key]?) ∧
      (∀ {count rom}, wordROMImage before count = some rom → wordROMImage after count = some rom) ∧
      (∀ {count logCapacity}, decoderSetupImage before count logCapacity = some setup →
        count ≤ 1048576 → ∀ entry ∈ setup.program, entry.SourceWith after decoderFields) := by
  obtain ⟨history, rows, after, complete, permutation, _, actual, matched⟩ :=
    projected_row_history hp inputs accepted decoded aligned
  have bytes := projected_history_rom_bytes inputs.architectural actual
  exact ⟨history, rows, after, complete, permutation, actual, matched, bytes,
    (fun image => rom_image_after_frame bytes image),
    fun image profile => setup_sources_after_history inputs.architectural actual image profile⟩

end Airbender.WordMemory.Proofs
