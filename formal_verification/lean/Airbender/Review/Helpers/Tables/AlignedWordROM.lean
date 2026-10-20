import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification
set_option autoImplicit false

/-- V2 AlignedRomRead uses a word index, retaining both native 16-bit outputs
    and the same full four-MiB image/UNIMP tail as WordROM. It is native tag 46;
    the byte-addressed RomRead table has tag 24. -/
def WordROM.alignedRow (rom : WordROM) (i : Fin 1048576) : Vector Nat 3 :=
  #v[i.val, (rom.word i.val).toNat % 65536, (rom.word i.val).toNat / 65536]

def romAlignedWordTable {p : Nat} [Fact p.Prime] (rom : WordROM) :
    Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2AlignedRomRead"
  length := 1048576
  row i := (rom.alignedRow i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (rom.alignedRow i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification
