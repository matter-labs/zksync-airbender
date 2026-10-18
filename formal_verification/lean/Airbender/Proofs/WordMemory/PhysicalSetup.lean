import Airbender.Review.Helpers.Tables.PhysicalSetup
import Airbender.Proofs.WordMemory.ArtifactChecks
import Airbender.Proofs.Mersenne31
import Airbender.Proofs.WordMemory.ROMBytePadding

namespace Airbender.WordMemory.Proofs
open Verification

private theorem push_payload {α : Type} {left right : Vector α 3} {a b : α}
    (same : left.push a = right.push b) : left = right := by
  ext i bound
  have selected := congrArg (fun v : Vector α 4 => v[i]) same
  simpa only [Vector.getElem_push, dif_pos bound] using selected

/-- Every physical ROM tuple comes from its actual ROM region; dummy/separator/
    padding rows cannot masquerade as ROM rows because their tags differ. -/
theorem physical_rom_lookup (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    NativeSetup.Contains rom 24 query ↔ (romWordTable rom).Contains #[] query := by
  change (∃ row : NativeSetup.Row, NativeSetup.genericRow rom row = query.push 24) ↔
    ∃ i : Fin 1048576, query = (rom.row i).map Nat.cast
  constructor
  · rintro ⟨row, same⟩
    unfold NativeSetup.genericRow at same
    split_ifs at same with dummy separator word
    · have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
      exact ((by decide : (0 : ZMod mersenne31Modulus) ≠ 24) (by simpa using tag)).elim
    · have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
      exact ((by decide : (23 : ZMod mersenne31Modulus) ≠ 24) (by simpa using tag)).elim
    · exact ⟨_, (push_payload same).symm⟩
    · have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
      exact ((by decide : (0 : ZMod mersenne31Modulus) ≠ 24) (by simpa using tag)).elim
  · rintro ⟨i, rfl⟩
    refine ⟨⟨65537 + i.val, by have := i.isLt; omega⟩, ?_⟩
    simp [NativeSetup.genericRow,
      show ¬65537 + i.val < 65537 by omega, show 65537 + i.val < 1114113 by have := i.isLt; omega]

/-- The separator region has exactly the existing three-column lookup meaning,
    with native tag 23 excluding the dummy, ROM and zero-padding regions. -/
theorem physical_separator_lookup (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    NativeSetup.Contains rom 23 query ↔ romSeparatorTable.Contains #[] query := by
  change (∃ row : NativeSetup.Row, NativeSetup.genericRow rom row = query.push 23) ↔
    ∃ i : Fin 65536, query = (romSeparatorRow i).map Nat.cast
  constructor
  · rintro ⟨row, same⟩
    unfold NativeSetup.genericRow at same
    split_ifs at same with dummy separator word
    · have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
      exact ((by decide : (0 : ZMod mersenne31Modulus) ≠ 23) (by simpa using tag)).elim
    · exact ⟨_, (push_payload same).symm⟩
    · have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
      exact ((by decide : (24 : ZMod mersenne31Modulus) ≠ 23) (by simpa using tag)).elim
    · have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
      exact ((by decide : (0 : ZMod mersenne31Modulus) ≠ 23) (by simpa using tag)).elim
  · rintro ⟨i, rfl⟩
    refine ⟨⟨1 + i.val, by have := i.isLt; omega⟩, ?_⟩
    simp [NativeSetup.genericRow,
      show 1 + i.val < 65537 by have := i.isLt; omega]

/-- Every unused active generic tuple has tag zero. In particular it cannot
    authenticate a ROM or separator query by matching its three values alone. -/
theorem physical_padding_tag (rom : WordROM) (row : NativeSetup.Row) (padding : 1114113 ≤ row.val) :
    (NativeSetup.genericRow (p := mersenne31Modulus) rom row)[3] = 0 := by
  simp [NativeSetup.genericRow, show row.val ≠ 0 by omega,
    show ¬row.val < 65537 by omega, show ¬row.val < 1114113 by omega]

/-- Complete public Sail extraction turns a tagged physical ROM query into its
    actual byte-memory read. Key/data bounds follow from the constructed rows. -/
theorem physical_rom_read {before : Reference.RiscV.Sail.State} {rom : WordROM}
    (image : wordROMImage before 1048576 = some rom)
    {key lo hi : ZMod mersenne31Modulus}
    (member : NativeSetup.Contains rom 24 #v[key, lo, hi]) :
    (Trace.Cell.ram (BitVec.ofNat 32 key.val)).read before =
      .ok (Arithmetic.Word.mk lo.val hi.val).toBitVec before := by
  have logical := (physical_rom_lookup rom _).mp member
  change ∃ i : Fin 1048576, #v[key, lo, hi] = (rom.row i).map Nat.cast at logical
  obtain ⟨i, row⟩ := logical
  have address := congrArg (fun q : Vector (ZMod mersenne31Modulus) 3 => q[0]) row
  have low := congrArg (fun q : Vector (ZMod mersenne31Modulus) 3 => q[1]) row
  have high := congrArg (fun q : Vector (ZMod mersenne31Modulus) 3 => q[2]) row
  simp only [WordROM.row, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ] at address low high
  have keyValue : key.val = 4 * i.val := by
    rw [address, ZMod.val_natCast_of_lt (by have := i.isLt; unfold mersenne31Modulus; omega)]
  have canonical := Trace.Proofs.word_of_pc_query (pc := rom.word i.val)
    (by decide : Arithmetic.limbBase < mersenne31Modulus) low high
  rw [keyValue, canonical, Arithmetic.Word.ofBitVec_roundtrip]
  exact (rom_image_reads image).2 i

/-- The explicit public loader supplies the full extraction required above;
    no padding-read, coverage or desired table-content premise is introduced. -/
theorem padded_physical_rom_read {before initial : Reference.RiscV.Sail.State} {rom : WordROM} {count : Nat}
    (image : paddedWordROMImage before count = some (initial, rom))
    {key lo hi : ZMod mersenne31Modulus}
    (member : NativeSetup.Contains rom 24 #v[key, lo, hi]) :
    (Trace.Cell.ram (BitVec.ofNat 32 key.val)).read initial =
      .ok (Arithmetic.Word.mk lo.val hi.val).toBitVec initial := by
  obtain ⟨prefixROM, source, rfl, rfl⟩ := padded_image_source image
  exact physical_rom_read (padded_rom_image source) member

end Airbender.WordMemory.Proofs
