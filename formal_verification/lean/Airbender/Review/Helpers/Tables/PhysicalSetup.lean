import Airbender.Review.Helpers.Tables.WordROM
import Airbender.Review.Helpers.Tables.SetupColumns

namespace Airbender.Verification.NativeSetup

/-- Active physical rows of the pinned v2 2^24 setup trace. The last row is
    reserved for c0 normalization and has no lookup-row meaning here. -/
abbrev Row := Fin 16777215

/-- Native word-memory generic tuples: the dummy row, all separator rows tagged
    23, all word-ROM rows tagged 24, then zero tuples. This is the row model of
    dump_tables/get_main_domain_trace, not a Rust/export/LDE refinement claim. -/
def genericRow {p : Nat} (rom : WordROM) (row : Row) : Vector (ZMod p) 4 :=
  if row.val = 0 then Vector.replicate 4 0
  else if h : row.val < 65537 then
    ((romSeparatorRow ⟨row.val - 1, by omega⟩).map Nat.cast).push 23
  else if h : row.val < 1114113 then
    ((rom.row ⟨row.val - 65537, by omega⟩).map Nat.cast).push 24
  else Vector.replicate 4 0

/-- Match the complete physical tuple, including its native table ID. Dummy
    and padding tuples remain in the domain; proofs must exclude wrong tags. -/
def Contains {p : Nat} (rom : WordROM) (tag : Nat) (query : Vector (ZMod p) 3) : Prop :=
  ∃ row : Row, genericRow rom row = query.push (tag : ZMod p)

end Airbender.Verification.NativeSetup
