import Airbender.Review.Helpers.Tables.Range

namespace Airbender.Verification

/-- Public ROM words for the native four-MiB profile. The entire remaining region
    is retained with native UNIMP padding. Rust export/state binding is separate. -/
structure WordROM where
  words : List (BitVec 32)
  capacity : words.length ≤ 1048576

/-- Native separator row: high address limb, RAM flag, low six high-limb bits. -/
def romSeparatorRow (i : Fin 65536) : Vector Nat 3 :=
  #v[i.val, if i.val < 64 then 0 else 1, i.val % 64]

def romSeparatorTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2RomAddressSpaceSeparator"
  length := 65536
  row i := (romSeparatorRow i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (romSeparatorRow i).map Nat.cast
  contains_iff _ := Iff.rfl
}

/-- Native ROM generator pads missing words with 0xc0001073, not zero. -/
def WordROM.word (rom : WordROM) (i : Nat) : BitVec 32 :=
  rom.words[i]?.getD (BitVec.ofNat 32 3221229683)

def WordROM.row (rom : WordROM) (i : Fin 1048576) : Vector Nat 3 :=
  #v[4 * i.val, (rom.word i.val).toNat % 65536, (rom.word i.val).toNat / 65536]

def romWordTable {p : Nat} [Fact p.Prime] (rom : WordROM) :
    Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2RomRead"
  length := 1048576
  row i := (rom.row i).map Nat.cast
  index query := query[0].val / 4
  Spec query := ∃ i, query = (rom.row i).map Nat.cast
  contains_iff _ := Iff.rfl
}

/-- Exact three-column native lookup; neither masking nor a disabled row is added. -/
def fixed3 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 3))
    (entry : Vector (Expression (ZMod p)) 3) : Lookup (ZMod p) where
  table := table.toRaw
  entry := entry

end Airbender.Verification
