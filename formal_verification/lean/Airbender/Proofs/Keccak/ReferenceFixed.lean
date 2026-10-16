import Airbender.Review.Circuits.Keccak.Tables.Setup

namespace Airbender.Keccak

/- Mathematical characterizations; circuit table contents are imported. -/
def byteRow (tag index : Nat) : Vector Nat 8 :=
  let a := if tag = 4 then index / 256 else index % 256
  let b := if tag = 4 then index % 256 else index / 256
  let c := if tag = 38 then a ^^^ iotaByte b
    else if tag = 39 then (a ^^^ 255) &&& b else a ^^^ b
  #v[a, b, c, 0, 0, 0, 0, tag]

def rotationRow (key : Nat) : Vector Nat 8 :=
  let word := key % 65536
  let shift := key / 65536
  #v[key, word / 2 ^ (16 - shift), (word * 2 ^ shift) % 65536, 0, 0, 0, 0, 40]

def referenceSetupRow (control : Fin 4096 → Vector Nat 6) (index : Fin 1249281) : Vector Nat 8 :=
  let n := index.val
  if n = 0 then Vector.replicate 8 0
  else if n < 65537 then byteRow 4 (n - 1)
  else if h : n < 69633 then
    let key : Fin 4096 := ⟨n - 65537, by omega⟩
    let outputs := control key
    #v[key.val, outputs[0], outputs[1], outputs[2], outputs[3], outputs[4], outputs[5], 37]
  else if n < 135169 then byteRow 38 (n - 69633)
  else if n < 200705 then byteRow 39 (n - 135169)
  else rotationRow (n - 200705)

end Airbender.Keccak
