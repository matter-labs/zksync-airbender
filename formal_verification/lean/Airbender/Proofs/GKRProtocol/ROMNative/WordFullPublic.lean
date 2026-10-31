import Airbender.Proofs.GKRProtocol.ROMNative.WordFullRows
import Airbender.Review.Compiler.ROMDomain
import Airbender.Proofs.GKRProtocol.ROMNative.WordMemoryPublic
import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Rows
import Airbender.Proofs.Trace.ROM

namespace Airbender.Compiler.ROMNative.WordFullPublic
open Airbender Airbender.Compiler Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem imported_public_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (physical : Trace.initialImage before cells = some tokens) (domain : CoversROM cells)
    {query : Vector Source.BaseField 9}
    (member : (Trace.ROM.importedTable (p := babyBearModulus)).Contains #[] query) :
    (Trace.ROM.table cells tokens).Contains #[] query := by
  suffices present : query ∈ Trace.ROM.rows cells tokens by
    obtain ⟨index, same⟩ := List.mem_iff_get.mp present
    exact ⟨index, same.symm⟩
  rcases Trace.ROM.Proofs.imported_member member with rfl | ⟨index, rfl⟩
  · exact List.mem_cons_self
  · let address := BitVec.ofNat 32 (4 * index.val)
    let bits := BitVec.ofNat 32 (Trace.ROM.Proofs.selectedWord index.val)
    have small : 4 * index.val < 2 ^ 32 := by have := index.isLt; omega
    have addressNat : address.toNat = 4 * index.val := Nat.mod_eq_of_lt small
    have read : (Trace.Cell.ram address).read before = .ok bits before := by
      change (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 address.toNat).run before = _
      rw [addressNat]
      exact image ⟨index.val, index.isLt⟩
    have zipped := image_zip_member physical (domain index) read
    have wordBound := Trace.ROM.Proofs.selectedWord_bound index.val index.isLt
    have same : Trace.ROM.row (p := babyBearModulus) address (Arithmetic.Word.ofBitVec bits) =
        (#v[4 * index.val, Trace.ROM.Proofs.selectedWord index.val % 65536,
          Trace.ROM.Proofs.selectedWord index.val / 65536, 0, 0, 0, 0, 0, 34] : Vector Nat 9).map
            (fun n : Nat => (n : Source.BaseField)) := by
      simp [Trace.ROM.row, Arithmetic.Word.ofBitVec, bits, addressNat,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound, Arithmetic.limbBase]
    rw [← same]
    apply List.mem_cons_of_mem
    apply List.mem_filterMap.mpr
    refine ⟨(Trace.Cell.ram address, (Trace.Cell.ram address).initialToken bits), zipped, ?_⟩
    simp only [addressNat, Trace.Proofs.initial_token_word]
    rw [if_pos (by have := index.isLt; dsimp [Trace.ROM.limit]; omega)]

theorem public_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (physical : Trace.initialImage before cells = some tokens) (domain : CoversROM cells)
    {query : Vector Source.BaseField 9}
    (member : (nativeSetup.imported.data.table "Airbender.Native.WordMemory").Contains #[] query)
    (notDecoder : query[8] ≠ 46) :
    (Trace.ROM.table cells tokens).Contains #[] query :=
  imported_public_refinement image physical domain (full_refinement member notDecoder)

end Airbender.Compiler.ROMNative.WordFullPublic
