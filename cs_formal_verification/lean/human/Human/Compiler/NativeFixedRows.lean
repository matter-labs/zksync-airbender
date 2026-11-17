module
public import Human.Circuits.UnifiedReduced.Tables.SetupRV
public import Human.Helpers.Tables.Subword
public import Human.Circuits.JumpBranchSlt.Tables.Control
public import Human.Compiler.NativeSetups.MulDiv
public import Human.Compiler.NativeSetups.WordMemory
public import Human.Compiler.NativeSetups.JumpBranch
public import Human.Compiler.NativeSetups.AddSub
public import Human.Compiler.NativeSetups.Rows

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

/-- Decoder slot `slot` of the add/sub setup for the setup fixture program. The fields are the PC limbs, `rs1`,
    `rs2`, `rd`, the immediate limbs and the mask. Slot 0 holds `addi x0, x0, 0`, slot 1 `addi x1, x1, 4` and slot 3
    `add x3, x3, x7`; every other slot holds the field element `-1` in each field. -/
def addSubFixtureDecoderRow (slot : Nat) : Vector Int 8 :=
  if slot = 0 then #v[0, 0, 0, 0, 0, 0, 0, 1]
  else if slot = 1 then #v[4, 0, 1, 0, 1, 4, 0, 1]
  else if slot = 3 then #v[12, 0, 3, 7, 3, 0, 0, 1]
  else Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)

/-- The add/sub setup has no fixed region: the decoder rows of the setup fixture program, then rows that hold the
    field element `-1` in each field, are the imported native rows on the complete trace domain. -/
def AddSubImportClaim : Prop :=
  NativeSetups.addSubSetup.traceLen = 16777216 ∧
  NativeSetups.addSubSetup.Rows fun index =>
    if index < 1048576 then addSubFixtureDecoderRow index
    else Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)

/-- Decoder slot `slot` of the jump/branch setup for the setup fixture program: slot 2 (PC 8) holds `jal x0, 0` (PC
    limbs 8 and 0, zero registers and immediate, mask 17), every other slot the field element `-1` in each payload
    field; the tag is 46. -/
def jumpBranchFixtureDecoderRow (slot : Nat) : Vector Int 10 :=
  if slot = 2 then #v[8, 0, 0, 0, 0, 0, 0, 0, 17, 46]
  else (Vector.replicate 9 ((babyBearModulus - 1 : Nat) : Int)).push 46

/-- The jump/branch fixed rows, the decoder rows of the setup fixture program, then zero padding, are the imported
    native rows on the complete trace domain. -/
def JumpBranchImportClaim : Prop :=
  NativeSetups.jumpBranchSetup.traceLen = 16777216 ∧
  NativeSetups.jumpBranchSetup.Rows fun index =>
    if bound : index < 4456448 then (jumpBranch ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else if index < 5505024 then jumpBranchFixtureDecoderRow (index - 4456448)
    else Vector.replicate 10 0

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

/-- The multiply/divide fixed rows, the decoder rows of the setup fixture program, then zero padding, are the imported
    native rows on the complete trace domain. The fixture program has no multiply or divide instruction: each decoder
    row holds the field element `-1` in every payload field and the tag 46. -/
def MulDivImportClaim : Prop :=
  NativeSetups.mulDivSetup.traceLen = 8388608 ∧
  NativeSetups.mulDivSetup.Rows fun index =>
    if bound : index < 270336 then (mulDiv ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else if index < 1318912 then (Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)).push 46
    else Vector.replicate 9 0

/-- The word-ROM rows of the setup fixture program, its decoder rows, then zero padding, are the imported native rows
    on the complete trace domain. The fixture program has no word load or store: each decoder row holds the field
    element `-1` in every payload field and the tag 46. -/
def WordMemoryImportClaim : Prop :=
  NativeSetups.wordMemorySetup.traceLen = 16777216 ∧
  NativeSetups.wordMemorySetup.Rows fun index =>
    if bound : index < 1048577 then
      (wordMemory NativeSetups.fixtureWords ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else if index < 2097153 then (Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)).push 46
    else Vector.replicate 9 0

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
