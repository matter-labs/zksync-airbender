import Human.Helpers.Memory.InitialImage
import Human.ISA.State

namespace Airbender.Trace.ROM
open Arithmetic

/-- Airbender's ROM/RAM split, used by the native word-memory lookup. -/
def limit : Nat := 4194304

/-- RV sibling of `words`: the word at byte address `4 * index` of the RV ROM image, read little-endian. Zero
    when the word lies past the RAM address range (`RV.RAM_END`), the same fallback as `words`. -/
def wordsRV (before : RV.State) (index : Nat) : BitVec 32 :=
  if 4 * index + 4 ≤ RV.RAM_END then RV.read before.rom (BitVec.ofNat 32 (4 * index)) 4 else 0

def row {p : Nat} (address : BitVec 32) (word : Word) : Vector (ZMod p) 9 :=
  #v[address.toNat, word.lo, word.hi, 0, 0, 0, 0, 0, 34]

/-- Modeled word-ROM rows: a zero disabled-query row, then one row for each
    public ROM cell paired with its seed value. Image binding must establish
    that `cells` and `tokens` describe the same public starting state. -/
def rows {p : Nat} (cells : List Cell) (tokens : List (MemoryToken p)) :
    List (Vector (ZMod p) 9) :=
  Vector.replicate 9 0 :: (cells.zip tokens).filterMap fun (cell, token) =>
    match cell with
    | .register _ => none
    | .ram address => if address.toNat < limit then some (row address token.word) else none

/-- The current modeled ROM format, instantiated with the public Sail image.
    The image equality binds the zipped cells/values; the zero row is the disabled
    query. This constructs no Rust setup artifact and proves no lookup argument. -/
def table {p : Nat} [Fact p.Prime] (cells : List Cell) (tokens : List (MemoryToken p)) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.PublicROM"
  length := (rows cells tokens).length
  row i := (rows cells tokens).get i
  index query := (rows cells tokens).toArray.findIdx (fun entry => entry == query)
  Spec query := query ∈ rows cells tokens
  contains_iff := by
    intro query
    constructor
    · rintro ⟨i, rfl⟩
      exact List.get_mem _ i
    · intro member
      obtain ⟨i, equal⟩ := List.mem_iff_get.mp member
      exact ⟨i, equal.symm⟩
}

end Airbender.Trace.ROM
