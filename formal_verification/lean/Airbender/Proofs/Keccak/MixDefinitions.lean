import Airbender.Review.Circuits.Keccak.Mix
import Airbender.Proofs.Arithmetic.ByteAssembly

namespace Airbender.Keccak.Proofs.Mix

def nativeLimbs (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 4, start + 5]
def temporary (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 2, start + 3]
def mixMode (second : Bool) : Fin 7 := if second then 2 else 1
def aColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[nativeLimbs 23, nativeLimbs 47, nativeLimbs 39, nativeLimbs 23, nativeLimbs 39]
  else #v[nativeLimbs 15, nativeLimbs 31, nativeLimbs 15, nativeLimbs 47, nativeLimbs 31]
def bColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[temporary 90, temporary 90, temporary 94, temporary 94, nativeLimbs 55]
  else #v[nativeLimbs 57, temporary 90, temporary 90, temporary 94, temporary 94]
def cColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[temporary 90, nativeLimbs 49, temporary 94, nativeLimbs 25, nativeLimbs 41]
  else #v[nativeLimbs 57, temporary 90, nativeLimbs 17, temporary 94, nativeLimbs 33]
def isRotation (second : Bool) (operation : Fin 5) : Bool :=
  if second then operation.val = 0 || operation.val = 2
  else operation.val = 0 || operation.val = 1 || operation.val = 3
def previous (i : Fin 4) : Fin 4 := ⟨(i.val + 3) % 4, by omega⟩
def packed {p : Nat} (w : Nat → ZMod p) (columns : Vector Nat 4) : Nat :=
  (w columns[0]).val + 65536 * ((w columns[1]).val +
    65536 * ((w columns[2]).val + 65536 * (w columns[3]).val))

end Airbender.Keccak.Proofs.Mix
