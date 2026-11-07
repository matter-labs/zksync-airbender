import Airbender.Review.Circuits.ReducedMachine.Tables.Native

namespace Airbender.ReducedMachine.NativeFixed

/-- Actual word-store offset and memory-space separator references. -/
def wordOffsetRow (key : Nat) : Vector Nat 4 := #v[key,key%2,key/2%2,18]

def wordSeparatorRow (key : Nat) : Vector Nat 4 :=
  #v[key,if key < 64 then 0 else 1,key%64,23]

/-- The eight-word native ROM fixture, with its last word repeated as padding.
    This reference is not an arbitrary original Sail program image. -/
def wordROMValue (index : Nat) : Vector Nat 2 :=
  match index with
  | 0 => #v[32947,16]
  | 1 => #v[33043,65520]
  | 2 => #v[32819,16416]
  | 3 => #v[29111,0]
  | 4 => #v[21015,0]
  | 5 => #v[41347,0]
  | 6 => #v[40995,32]
  | _ => #v[4211,49152]

def wordROMRow (index : Nat) : Vector Nat 4 :=
  #v[4*index,(wordROMValue index)[0],(wordROMValue index)[1],24]

end Airbender.ReducedMachine.NativeFixed
