module
public import Human.Circuits.UnifiedReduced.Tables.SetupRV
public import Human.Helpers.Tables.Subword
public import Human.Circuits.JumpBranchSlt.Tables.Control

@[expose] public section
namespace Airbender.Compiler.NativeFixedRows
open Airbender Trace Arithmetic Verification

/-- The complete native tagged conditional/control setup. -/
def jumpBranch (index : Fin 4456448) : Vector Nat 10 :=
  let n := index.val
  if n < 131072 then #v[n, if n = 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 1]
  else if n < 196608 then
    let key := n - 131072
    #v[key, key / 2 % 2, key - key % 4, 0, 0, 0, 0, 0, 0, 2]
  else if n < 262144 then
    let key := n - 196608
    #v[key, key / 32768, 0, 0, 0, 0, 0, 0, 0, 5]
  else
    let key := n - 262144
    #v[key, conditionalValue key, 0, 0, 0, 0, 0, 0, 0, 31]

/-- Native multiply/divide setup regions. Table 10 has two eight-bit keys. -/
def mulDiv (index : Fin 270336) : Vector Nat 9 :=
  let n := index.val
  if n < 131072 then #v[n, if n = 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 1]
  else if n < 196608 then
    let key := n - 131072
    #v[key / 256, key % 256, 0, 0, 0, 0, 0, 0, 10]
  else if n < 204800 then
    #v[n - 196608, 0, 0, 0, 0, 0, 0, 0, 26]
  else
    let key := n - 204800
    #v[key, key % 256, 0, 0, 0, 0, 0, 0, 41]

/-- Native word-ROM region. Index zero is the disabled-query row. -/
def wordMemory (words : Nat → BitVec 32) (index : Fin 1048577) : Vector Nat 9 :=
  if index.val = 0 then Vector.replicate 9 0 else
    let key := index.val - 1
    let word := Word.ofBitVec (words key)
    #v[4 * key, word.lo, word.hi, 0, 0, 0, 0, 0, 34]

/-- Reorder native unified regions into the retained logical table order.
    Both orders retain every key, output, tag and ROM word. -/
def unifiedIndex (index : Fin 2097537) : Fin 2097537 :=
  let n := index.val
  ⟨if n = 0 then 0
    else if n < 131073 then 524545 + (n - 1)
    else if n < 196609 then 721153 + (n - 131073)
    else if n < 196865 then 1 + (n - 196609)
    else if n < 262401 then 655617 + (n - 196865)
    else if n < 327937 then 196865 + (n - 262401)
    else if n < 590081 then 262401 + (n - 327937)
    else if n < 1638657 then 1048961 + (n - 590081)
    else if n < 1900801 then 786817 + (n - 1638657)
    else if n < 1900929 then 786689 + (n - 1900801)
    else 257 + (n - 1900929), by
      have bound := index.isLt
      dsimp [n] at *
      split_ifs <;> omega⟩

/-- The current unified logical rows at their native physical region positions. -/
def unified (words : Nat → BitVec 32) (index : Fin 2097537) : Vector Nat 10 :=
  UnifiedReduced.Setup.rowWith words (unifiedIndex index)

end Airbender.Compiler.NativeFixedRows
