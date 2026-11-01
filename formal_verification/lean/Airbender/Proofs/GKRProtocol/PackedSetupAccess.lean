import Airbender.Proofs.GKRProtocol.PackedSetupEquality

namespace Airbender.Compiler.PackedSetupAccess
open Airbender.Setup PackedSetupEquality
set_option warningAsError true

def arrayGet : ArrayCode → Nat → Option Nat
  | .literal length payload, index => (bytes length payload)[index]?
  | .append left right, index =>
      if index < left.length then arrayGet left index else arrayGet right (index - left.length)
  | .constant length value, index => if index < length then some value else none
  | .range length, index => if index < length then some index else none
  | .linear length first, index => if index < length then some (first + index) else none
  | .rotate length first, index => if index < length then some ((first + index) % length) else none
  | .linearRuns length first step run, index =>
      if index < length then some (first + step * (index / run)) else none
  | .lookupRuns length run values, index =>
      if index < length then some ((arrayGet values (index / run)).getD 0) else none
  | .packedBytes length payload, index =>
      if index < length then some (packedByte payload index) else none

theorem arrayGet_decode (code : ArrayCode) (index : Nat) :
    code.decode[index]? = arrayGet code index := by
  induction code generalizing index with
  | literal length payload => simp [arrayGet, ArrayCode.decode]
  | append left right first second =>
      simp [arrayGet, ArrayCode.decode, Array.getElem?_append, ArrayCode.decode_length, first, second]
  | constant length value => simp [arrayGet, ArrayCode.decode, Array.getElem?_replicate]
  | range length => simp [arrayGet, ArrayCode.decode, Array.getElem?_range]
  | linear length first => simp [arrayGet, ArrayCode.decode, Array.getElem?_ofFn]
  | rotate length first => simp [arrayGet, ArrayCode.decode, Array.getElem?_ofFn]
  | linearRuns length first step run => simp [arrayGet, ArrayCode.decode, Array.getElem?_ofFn]
  | lookupRuns length run values ih => simp [arrayGet, ArrayCode.decode, Array.getElem?_ofFn, ih]
  | packedBytes length payload => simp [arrayGet, ArrayCode.decode, packedArray, Array.getElem?_ofFn]

def blockGet (block : BlockCode) (index : Nat) : Option Nat :=
  if index < block.length then
    match block with
    | .affine _ first step =>
        let value := (first : Int) + step * index
        if 0 ≤ value then some value.toNat else none
    | .dense values => arrayGet values index
    | .periodic _ stride values =>
        let value := ((arrayGet values (index % values.length)).getD 0 : Int) + stride * (index / values.length)
        if 0 ≤ value then some value.toNat else none
  else none

theorem blockGet_decode (code : BlockCode) (index : Nat) :
    code.decode.get? index = blockGet code index := by
  cases code <;>
    simp [blockGet, Block.get?, BlockCode.length, Block.length, ArrayCode.decode_length, arrayGet_decode]

end Airbender.Compiler.PackedSetupAccess
