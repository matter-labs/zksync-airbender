import Airbender.Review.Trace.InitialImage

namespace Airbender.Trace.ROM
open Arithmetic

/-- Airbender's ROM/RAM split, used by the native word-memory lookup. -/
def limit : Nat := 4194304

def row {p : Nat} (address : BitVec 32) (word : Word) : Vector (ZMod p) 9 :=
  #v[address.toNat, word.lo, word.hi, 0, 0, 0, 0, 0, 34]

/-- Uniform ROM binding needed by the word-memory proof. Every active table
    query agrees with an actual read of the supplied Sail state. -/
def Reads {p : Nat} [Fact p.Prime] (before : Reference.RiscV.Sail.State)
    (rom : Table (ZMod p) (fields 9)) : Prop :=
  ∀ (address : Word) (lo hi : ZMod p), address.Bounded → address.hi < 64 →
    rom.Contains #[] #v[(address.lo : ZMod p) + 65536 * address.hi,
      lo, hi, 0, 0, 0, 0, 0, 34] →
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 address.toBitVec.toNat).run before =
      .ok (Word.mk lo.val hi.val).toBitVec before

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
