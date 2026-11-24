module
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedNumericData.Part011
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

open NumericPolynomialChecks

def numericBackward.leaf12 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 282)], [([((1 : Nat), [])], 283)], [([((1 : Nat), [])], 284)], [([((1 : Nat), [])], 285)],
    [([((1 : Nat), [])], 286)], [([((1 : Nat), [])], 287)], [([((1 : Nat), [])], 288)], [([((1 : Nat), [])], 289)],
    [([((1 : Nat), [])], 290)], [([((1 : Nat), [])], 291)], [([((1 : Nat), [])], 292)], [([((1 : Nat), [])], 293)],
    [([((1 : Nat), [])], 294)], [([((1 : Nat), [])], 295)], [([((1 : Nat), [])], 296)], [([((1 : Nat), [])], 297)]]

def numericBackward.leaf13 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 298)], [([((1 : Nat), [])], 299)], [([((1 : Nat), [])], 300)], [([((1 : Nat), [])], 301)],
    [([((1 : Nat), [])], 302)], [([((1 : Nat), [])], 303)], [([((1 : Nat), [])], 304)], [([((1 : Nat), [])], 305)],
    [([((1 : Nat), [])], 306)], [([((1 : Nat), [])], 307)], [([((1 : Nat), [])], 308)], [([((1 : Nat), [])], 309)]]

def numericBackward : List (List (NumericPolynomialChecks.Data × Nat)) :=
  List.append
    (List.append (List.append numericBackward.leaf0 (List.append numericBackward.leaf1 numericBackward.leaf2))
      (List.append (List.append numericBackward.leaf3 numericBackward.leaf4)
        (List.append numericBackward.leaf5 numericBackward.leaf6)))
    (List.append (List.append numericBackward.leaf7 (List.append numericBackward.leaf8 numericBackward.leaf9))
      (List.append (List.append numericBackward.leaf10 numericBackward.leaf11)
        (List.append numericBackward.leaf12 numericBackward.leaf13)))

def numericBackward.tree : NumericPolynomialChecks.LookupTable (List (NumericPolynomialChecks.Data × Nat)) :=
  NumericPolynomialChecks.LookupTable.branch 112
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf0)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf1)
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf2)))
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf3)
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf4))
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf5)
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf6))))
    (NumericPolynomialChecks.LookupTable.branch 48
      (NumericPolynomialChecks.LookupTable.branch 16 (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf7)
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf8)
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf9)))
      (NumericPolynomialChecks.LookupTable.branch 32
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf10)
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf11))
        (NumericPolynomialChecks.LookupTable.branch 16
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf12)
          (NumericPolynomialChecks.LookupTable.leaf numericBackward.leaf13))))

theorem numericBackward.tree_binding : (numericBackward.tree).toList = numericBackward := by kernel_rfl

theorem numericBackward.tree_valid : (numericBackward.tree).valid = true := by kernel_rfl

def numericForward.leaf0 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def numericForward.leaf1 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def numericForward.leaf2 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def numericForward.leaf3 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def numericForward.leaf4 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def numericForward.leaf5 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[], [], [], [], [], [], [], [], [], [], [([((1 : Nat), [])], 0)], [([((1 : Nat), [])], 1)],
    [([((1 : Nat), [])], 2)], [([((1 : Nat), [])], 3)], [([((1 : Nat), [])], 4)], [([((1 : Nat), [])], 5)]]

def numericForward.leaf6 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 6)], [([((1 : Nat), [])], 7)], [([((1 : Nat), [])], 8)], [([((1 : Nat), [])], 9)],
    [([((1 : Nat), [])], 10)], [([((1 : Nat), [])], 11)], [([((1 : Nat), [])], 12)], [([((1 : Nat), [])], 13)],
    [([((1 : Nat), [])], 14)], [([((1 : Nat), [])], 15)], [([((1 : Nat), [])], 16)], [([((1 : Nat), [])], 17)],
    [([((1 : Nat), [])], 18)], [([((1 : Nat), [])], 19)], [([((1 : Nat), [])], 20)], [([((1 : Nat), [])], 21)]]

def numericForward.leaf7 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 22)], [([((1 : Nat), [])], 23)], [([((1 : Nat), [])], 24)], [([((1 : Nat), [])], 25)],
    [([((1 : Nat), [])], 26)], [([((1 : Nat), [])], 27)], [([((1 : Nat), [])], 28)], [([((1 : Nat), [])], 29)],
    [([((1 : Nat), [])], 30)], [([((1 : Nat), [])], 31)], [([((1 : Nat), [])], 32)], [([((1 : Nat), [])], 33)],
    [([((1 : Nat), [])], 34)], [([((1 : Nat), [])], 35)], [([((1 : Nat), [])], 36)], [([((1 : Nat), [])], 37)]]

def numericForward.leaf8 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 38)], [([((1 : Nat), [])], 39)], [([((1 : Nat), [])], 40)], [([((1 : Nat), [])], 41)],
    [([((1 : Nat), [])], 42)], [([((1 : Nat), [])], 43)], [([((1 : Nat), [])], 44)], [([((1 : Nat), [])], 45)],
    [([((1 : Nat), [])], 46)], [([((1 : Nat), [])], 47)], [([((1 : Nat), [])], 48)], [([((1 : Nat), [])], 49)],
    [([((1 : Nat), [])], 50)], [([((1 : Nat), [])], 51)], [([((1 : Nat), [])], 52)], [([((1 : Nat), [])], 53)]]

def numericForward.leaf9 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 54)], [([((1 : Nat), [])], 55)], [([((1 : Nat), [])], 56)], [([((1 : Nat), [])], 57)],
    [([((1 : Nat), [])], 58)], [([((1 : Nat), [])], 59)], [([((1 : Nat), [])], 60)], [([((1 : Nat), [])], 61)],
    [([((1 : Nat), [])], 62)], [([((1 : Nat), [])], 63)], [([((1 : Nat), [])], 64)], [([((1 : Nat), [])], 65)],
    [([((1 : Nat), [])], 66)], [([((1 : Nat), [])], 67)], [([((1 : Nat), [])], 68)], [([((1 : Nat), [])], 69)]]

def numericForward.leaf10 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 70)], [([((1 : Nat), [])], 71)], [([((1 : Nat), [])], 72)], [([((1 : Nat), [])], 73)],
    [([((1 : Nat), [])], 74)], [([((1 : Nat), [])], 75)], [([((1 : Nat), [])], 76)], [([((1 : Nat), [])], 77)],
    [([((1 : Nat), [])], 78)], [([((1 : Nat), [])], 79)], [([((1 : Nat), [])], 80)], [([((1 : Nat), [])], 81)],
    [([((1 : Nat), [])], 82)], [([((1 : Nat), [])], 83)], [([((1 : Nat), [])], 84)], [([((1 : Nat), [])], 85)]]

def numericForward.leaf11 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 86)], [([((1 : Nat), [])], 87)], [([((1 : Nat), [])], 88)], [([((1 : Nat), [])], 89)],
    [([((1 : Nat), [])], 90)], [([((1 : Nat), [])], 91)], [([((1 : Nat), [])], 92)], [([((1 : Nat), [])], 93)],
    [([((1 : Nat), [])], 94)], [([((1 : Nat), [])], 95)], [([((1 : Nat), [])], 96)], [([((1 : Nat), [])], 97)],
    [([((1 : Nat), [])], 98)], [([((1 : Nat), [])], 99)], [([((1 : Nat), [])], 100)], [([((1 : Nat), [])], 101)]]

def numericForward.leaf12 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 102)], [([((1 : Nat), [])], 103)], [([((1 : Nat), [])], 104)], [([((1 : Nat), [])], 105)],
    [([((1 : Nat), [])], 106)], [([((1 : Nat), [])], 107)], [([((1 : Nat), [])], 108)], [([((1 : Nat), [])], 109)],
    [([((1 : Nat), [])], 110)], [([((1 : Nat), [])], 111)], [([((1 : Nat), [])], 112)], [([((1 : Nat), [])], 113)],
    [([((1 : Nat), [])], 114)], [([((1 : Nat), [])], 115)], [([((1 : Nat), [])], 116)], [([((1 : Nat), [])], 117)]]

def numericForward.leaf13 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 118)], [([((1 : Nat), [])], 119)], [([((1 : Nat), [])], 120)], [([((1 : Nat), [])], 121)],
    [([((1 : Nat), [])], 122)], [([((1 : Nat), [])], 123)], [([((1 : Nat), [])], 124)], [([((1 : Nat), [])], 125)],
    [([((1 : Nat), [])], 126)], [([((1 : Nat), [])], 127)], [([((1 : Nat), [])], 128)], [([((1 : Nat), [])], 129)],
    [([((1 : Nat), [])], 130)], [([((1 : Nat), [])], 131)], [([((1 : Nat), [])], 132)], [([((1 : Nat), [])], 133)]]

def numericForward.leaf14 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 134)], [([((1 : Nat), [])], 135)], [([((1 : Nat), [])], 136)], [([((1 : Nat), [])], 137)],
    [([((1 : Nat), [])], 138)], [([((1 : Nat), [])], 139)], [([((1 : Nat), [])], 140)], [([((1 : Nat), [])], 141)],
    [([((1 : Nat), [])], 142)], [([((1 : Nat), [])], 143)], [([((1 : Nat), [])], 144)], [([((1 : Nat), [])], 145)],
    [([((1 : Nat), [])], 146)], [([((1 : Nat), [])], 147)], [([((1 : Nat), [])], 148)], [([((1 : Nat), [])], 149)]]

def numericForward.leaf15 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 150)], [([((1 : Nat), [])], 151)], [([((1 : Nat), [])], 152)], [([((1 : Nat), [])], 153)],
    [([((1 : Nat), [])], 154)], [([((1 : Nat), [])], 155)], [([((1 : Nat), [])], 156)], [([((1 : Nat), [])], 157)],
    [([((1 : Nat), [])], 158)], [([((1 : Nat), [])], 159)], [([((1 : Nat), [])], 160)], [([((1 : Nat), [])], 161)],
    [([((1 : Nat), [])], 162)], [([((1 : Nat), [])], 163)], [([((1 : Nat), [])], 164)], [([((1 : Nat), [])], 165)]]

def numericForward.leaf16 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 166)], [([((1 : Nat), [])], 167)], [([((1 : Nat), [])], 168)], [([((1 : Nat), [])], 169)],
    [([((1 : Nat), [])], 170)], [([((1 : Nat), [])], 171)], [([((1 : Nat), [])], 172)], [([((1 : Nat), [])], 173)],
    [([((1 : Nat), [])], 174)], [([((1 : Nat), [])], 175)], [([((1 : Nat), [])], 176)], [([((1 : Nat), [])], 177)],
    [([((1 : Nat), [])], 178)], [([((1 : Nat), [])], 179)], [([((1 : Nat), [])], 180)], [([((1 : Nat), [])], 181)]]

def numericForward.leaf17 : List (List (NumericPolynomialChecks.Data × Nat)) :=
  [[([((1 : Nat), [])], 182)], [([((1 : Nat), [])], 183)], [([((1 : Nat), [])], 184)], [([((1 : Nat), [])], 185)],
    [([((1 : Nat), [])], 186)], [([((1 : Nat), [])], 187)], [([((1 : Nat), [])], 188)], [([((1 : Nat), [])], 189)],
    [([((1 : Nat), [])], 190)], [([((1 : Nat), [])], 191)], [([((1 : Nat), [])], 192)], [([((1 : Nat), [])], 193)],
    [([((1 : Nat), [])], 194)], [([((1 : Nat), [])], 195)], [([((1 : Nat), [])], 196)], [([((1 : Nat), [])], 197)]]
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
