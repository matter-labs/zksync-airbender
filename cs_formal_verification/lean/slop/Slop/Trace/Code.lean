import Slop.Trace.Addresses
import Slop.Trace.ROM
import Slop.WordMemory
import Slop.Sail.WordMemoryState

namespace Airbender.Trace.Proofs
open Arithmetic
open Reference.RiscV.Sail

/-- The native writable port of a selected SW addresses RAM. Its bounds come
    from the public cell image, and the ROM exclusion from imported equations. -/
theorem native_store_address [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    (selected : w 10 = 1) :
    (Word.mk (w 25).val (w 26).val).Bounded ∧
      ROM.limit ≤ (Word.mk (w 25).val (w 26).val).toBitVec.toNat := by
  let row : Row p := ⟨.wordMemory, w⟩
  have present : WordMemory.importedConstraintsMemoryPorts[2] ∈ row.ports := by
    simp [row, Row.ports, WordMemory.importedConstraintsMemoryPorts]
  have bound := address_bounds hp inverse accepted boundary image row member _ present
  change (Word.mk (w 25).val (w 26).val).Bounded at bound
  have constraints := accepted.constraints row member
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left (WordMemory.importedConstraints trace.rom)
      WordMemory.importedConstraintsTimestampLookups)
  have ram := (WordMemory.Proofs.rom_selection (by dsimp [timestampBase] at hp; omega)
    true core selected (by simp [row]) bound).2 rfl
  change 64 ≤ (w 26).val at ram
  refine ⟨bound, ?_⟩
  rw [Word.toBitVec_toNat bound]
  dsimp [ROM.limit, Word.value, limbBase]
  omega

/-- The public ROM word domain is aligned and ends before RAM. The native SW
    projection preserves its actual Sail byte reads; no expected read is assumed. -/
theorem native_store_code_frame [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    (selected : w 10 = 1) {before : Reference.RiscV.Sail.State}
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit) (aligned : pc.toNat % 4 = 0)
    {bits : BitVec 32} (read : (Cell.ram pc).read before = .ok bits before) :
    ∃ after, Reference.Sail.run
      (writeMemory (size := 4) (Word.mk (w 25).val (w 26).val).toBitVec
        (Word.mk (w 31).val (w 32).val).toBitVec) before = .ok () after ∧
      (Cell.ram pc).read after = .ok bits after := by
  have address := (native_store_address hp inverse accepted boundary image member selected).2
  let destination := (Word.mk (w 25).val (w 26).val).toBitVec
  let value := (Word.mk (w 31).val (w 32).val).toBitVec
  refine ⟨wordWriteState before destination.toNat value,
    write_word_state before destination value, ?_⟩
  apply written_word_disjoint destination.toNat value _ read
  left
  dsimp [ROM.limit] at inROM address
  change 4194304 ≤ destination.toNat at address
  omega

end Airbender.Trace.Proofs
