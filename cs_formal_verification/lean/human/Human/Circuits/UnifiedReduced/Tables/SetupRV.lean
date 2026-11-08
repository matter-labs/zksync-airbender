module
public import Human.Circuits.UnifiedReduced.Tables.Setup

@[expose] public section

/-! The same fixed rows, with the ROM words read from an `RV.State`. `rowWith`/`tableWith`
    are `row`/`table` with the ROM word function as a parameter; `tableRV` reads it with `ROM.wordsRV`. -/

namespace Airbender.UnifiedReduced.Setup
open Verification Trace

/-- `row` with the ROM words given by `words` (`words key` is the word at byte address `4 * key`). -/
def rowWith (words : Nat → BitVec 32) (index : Fin 2097537) : Vector Nat 10 :=
  if h : index.val < 1048961 then fixedRow ⟨index.val, h⟩ else
    let key := index.val - 1048961
    let word := Arithmetic.Word.ofBitVec (words key)
    #v[4 * key, word.lo, word.hi, 0, 0, 0, 0, 0, 0, 34]

/-- `table` with the ROM words given by `words`. -/
def tableWith {p : Nat} [Fact p.Prime] (words : Nat → BitVec 32) :
    Table (ZMod p) (fields 10) := .fromStatic {
  name := "Airbender.UnifiedReduced"
  length := 2097537
  row i := (rowWith words i).map (fun (n : Nat) => (n : ZMod p))
  index query := match query[9].val with
    | 0 => 0
    | 3 => 1 + query[0].val
    | 52 => 257 + query[0].val * 256 + query[1].val
    | 53 => 65793 + query[0].val * 256 + query[1].val
    | 54 => 131329 + query[0].val * 256 + query[1].val
    | 8 => 196865 + query[0].val * 256 + query[1].val
    | 9 => 262401 + query[0].val * 65536 + query[1].val * 256 + query[2].val * 8 + query[3].val
    | 1 => 524545 + query[0].val
    | 5 => 655617 + query[0].val
    | 2 => 721153 + query[0].val
    | 51 => 786689 + query[0].val
    | 47 | 48 | 49 | 50 => 786817 + (query[9].val - 47) * 65536 + query[0].val * 256 + query[1].val
    | 34 => 1048961 + query[0].val / 4
    | _ => 0
  Spec query := ∃ i : Fin 2097537, query = (rowWith words i).map (fun (n : Nat) => (n : ZMod p))
  contains_iff _ := Iff.rfl
}

/-- The unified setup table of the public RV starting state: ROM words read by `RV.read` (`ROM.wordsRV`). -/
abbrev tableRV {p : Nat} [Fact p.Prime] (initial : RV.State) : Table (ZMod p) (fields 10) :=
  tableWith (ROM.wordsRV initial)

end Airbender.UnifiedReduced.Setup
