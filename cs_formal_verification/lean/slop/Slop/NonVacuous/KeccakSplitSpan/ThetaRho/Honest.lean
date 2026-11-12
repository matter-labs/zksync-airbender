module
public import Slop.NonVacuous.KeccakSplitSpan.Common

@[expose] public section

/-! The honest assignment of one theta+rho row (`ThetaRho.importedConstraints`' columns, numbered as the artifact
    numbers them), computed from the row's inputs: `D` byte-wise from `C[x-1]` and `C[x+1]` rotated by one, each
    lane byte XORed with `D` and split at the column's rho offset mod 8 (`frag0`, `frag1`), and each written limb
    the bytes those fragments place, as the rotation equations weigh them under the one-hot column flags. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

/-- The rho offset of lane (c, y), as the rotation equations weigh it (`KECCAK_F1600_RHO`). -/
def rho (c y : Nat) : Nat :=
  ([[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14]].getD c []).getD y 0

variable (x : RowInput)

/-- One-hot flag `f` of the call's column. -/
def flag (f : Nat) : Nat := if x.call % 5 = f then 1 else 0

/-- The top bit of limb `m` of `C[x+1]`. -/
def top (m : Nat) : Nat := x.limb 6 m / 32768

/-- Limb `m` of `C[x+1]` rotated left by one (64 bits). -/
def rotLimb (m : Nat) : Nat := 2 * x.limb 6 m % 65536 + top x ((m + 3) % 4)

/-- Byte `j` of `C[x-1]`, of `C[x+1]` rotated, and of `D`. -/
def cByte (j : Nat) : Nat := if j % 2 = 0 then x.limb 5 (j / 2) % 256 else x.limb 5 (j / 2) / 256
def rByte (j : Nat) : Nat := if j % 2 = 0 then rotLimb x (j / 2) % 256 else rotLimb x (j / 2) / 256
def d (j : Nat) : Nat := cByte x j ^^^ rByte x j

/-- The rho offset mod 8 of lane `y` in the call's column. -/
def shift (y : Nat) : Nat := rho (x.call % 5) y % 8

/-- Byte `j` of lane `y`, XORed with `D`, and its two fragments at the lane's shift. -/
def inByte (y j : Nat) : Nat := if j % 2 = 0 then x.limb y (j / 2) % 256 else x.limb y (j / 2) / 256
def frag0 (y j : Nat) : Nat := (inByte x y j ^^^ d x j) * 2 ^ shift x y % 256
def frag1 (y j : Nat) : Nat := (inByte x y j ^^^ d x j) / 2 ^ (8 - shift x y)

/-- Byte `k` of the written lane `y`: fragment 0 of byte `k - q`, plus fragment 1 of byte `k - q - 1` unless the
    offset `8 q + s` has `s = 0`. -/
def outByte (y k : Nat) : Nat :=
  frag0 x y ((k + 8 - rho (x.call % 5) y / 8) % 8) +
    if rho (x.call % 5) y % 8 = 0 then 0 else frag1 x y ((k + 7 - rho (x.call % 5) y / 8) % 8)

/-- Limb `m` of the written lane `y`. -/
def out (y m : Nat) : Nat := outByte x y (2 * m) + 256 * outByte x y (2 * m + 1)

/-- The honest value of every column. -/
def column : Nat → Nat
  | 0 => 1
  | 1 => x.invocation
  | 2 => 0
  | 3 => x.control
  | 4 => 0
  | 5 => bump x.control
  | 6 => 0
  | 7 => slotNat x.call 0
  | 8 => slotNat x.call 1
  | 9 => slotNat x.call 2
  | 10 => slotNat x.call 3
  | 11 => slotNat x.call 4
  | 12 => slotNat x.call 5
  | 13 => slotNat x.call 6
  | 14 => (x.read 1).lo
  | 15 => (x.read 1).hi
  | 16 => x.limb 0 0
  | 17 => x.limb 0 1
  | 18 => out x 0 0
  | 19 => out x 0 1
  | 20 => x.limb 0 2
  | 21 => x.limb 0 3
  | 22 => out x 0 2
  | 23 => out x 0 3
  | 24 => x.limb 1 0
  | 25 => x.limb 1 1
  | 26 => out x 1 0
  | 27 => out x 1 1
  | 28 => x.limb 1 2
  | 29 => x.limb 1 3
  | 30 => out x 1 2
  | 31 => out x 1 3
  | 32 => x.limb 2 0
  | 33 => x.limb 2 1
  | 34 => out x 2 0
  | 35 => out x 2 1
  | 36 => x.limb 2 2
  | 37 => x.limb 2 3
  | 38 => out x 2 2
  | 39 => out x 2 3
  | 40 => x.limb 3 0
  | 41 => x.limb 3 1
  | 42 => out x 3 0
  | 43 => out x 3 1
  | 44 => x.limb 3 2
  | 45 => x.limb 3 3
  | 46 => out x 3 2
  | 47 => out x 3 3
  | 48 => x.limb 4 0
  | 49 => x.limb 4 1
  | 50 => out x 4 0
  | 51 => out x 4 1
  | 52 => x.limb 4 2
  | 53 => x.limb 4 3
  | 54 => out x 4 2
  | 55 => out x 4 3
  | 56 => x.limb 5 0
  | 57 => x.limb 5 1
  | 58 => x.limb 5 2
  | 59 => x.limb 5 3
  | 60 => x.limb 6 0
  | 61 => x.limb 6 1
  | 62 => x.limb 6 2
  | 63 => x.limb 6 3
  | 64 => x.limb 5 0 % 256
  | 65 => x.limb 5 1 % 256
  | 66 => x.limb 5 2 % 256
  | 67 => x.limb 5 3 % 256
  | 68 => top x 0
  | 69 => top x 1
  | 70 => top x 2
  | 71 => top x 3
  | 72 => rotLimb x 0 % 256
  | 73 => rotLimb x 1 % 256
  | 74 => rotLimb x 2 % 256
  | 75 => rotLimb x 3 % 256
  | 76 => d x 0
  | 77 => d x 1
  | 78 => d x 2
  | 79 => d x 3
  | 80 => d x 4
  | 81 => d x 5
  | 82 => d x 6
  | 83 => d x 7
  | 84 => flag x 0
  | 85 => flag x 1
  | 86 => flag x 2
  | 87 => flag x 3
  | 88 => flag x 4
  | 89 => x.limb 0 0 % 256
  | 90 => x.limb 0 1 % 256
  | 91 => x.limb 0 2 % 256
  | 92 => x.limb 0 3 % 256
  | 93 => frag0 x 0 0
  | 94 => frag1 x 0 0
  | 95 => frag0 x 0 1
  | 96 => frag1 x 0 1
  | 97 => frag0 x 0 2
  | 98 => frag1 x 0 2
  | 99 => frag0 x 0 3
  | 100 => frag1 x 0 3
  | 101 => frag0 x 0 4
  | 102 => frag1 x 0 4
  | 103 => frag0 x 0 5
  | 104 => frag1 x 0 5
  | 105 => frag0 x 0 6
  | 106 => frag1 x 0 6
  | 107 => frag0 x 0 7
  | 108 => frag1 x 0 7
  | 109 => x.limb 1 0 % 256
  | 110 => x.limb 1 1 % 256
  | 111 => x.limb 1 2 % 256
  | 112 => x.limb 1 3 % 256
  | 113 => frag0 x 1 0
  | 114 => frag1 x 1 0
  | 115 => frag0 x 1 1
  | 116 => frag1 x 1 1
  | 117 => frag0 x 1 2
  | 118 => frag1 x 1 2
  | 119 => frag0 x 1 3
  | 120 => frag1 x 1 3
  | 121 => frag0 x 1 4
  | 122 => frag1 x 1 4
  | 123 => frag0 x 1 5
  | 124 => frag1 x 1 5
  | 125 => frag0 x 1 6
  | 126 => frag1 x 1 6
  | 127 => frag0 x 1 7
  | 128 => frag1 x 1 7
  | 129 => x.limb 2 0 % 256
  | 130 => x.limb 2 1 % 256
  | 131 => x.limb 2 2 % 256
  | 132 => x.limb 2 3 % 256
  | 133 => frag0 x 2 0
  | 134 => frag1 x 2 0
  | 135 => frag0 x 2 1
  | 136 => frag1 x 2 1
  | 137 => frag0 x 2 2
  | 138 => frag1 x 2 2
  | 139 => frag0 x 2 3
  | 140 => frag1 x 2 3
  | 141 => frag0 x 2 4
  | 142 => frag1 x 2 4
  | 143 => frag0 x 2 5
  | 144 => frag1 x 2 5
  | 145 => frag0 x 2 6
  | 146 => frag1 x 2 6
  | 147 => frag0 x 2 7
  | 148 => frag1 x 2 7
  | 149 => x.limb 3 0 % 256
  | 150 => x.limb 3 1 % 256
  | 151 => x.limb 3 2 % 256
  | 152 => x.limb 3 3 % 256
  | 153 => frag0 x 3 0
  | 154 => frag1 x 3 0
  | 155 => frag0 x 3 1
  | 156 => frag1 x 3 1
  | 157 => frag0 x 3 2
  | 158 => frag1 x 3 2
  | 159 => frag0 x 3 3
  | 160 => frag1 x 3 3
  | 161 => frag0 x 3 4
  | 162 => frag1 x 3 4
  | 163 => frag0 x 3 5
  | 164 => frag1 x 3 5
  | 165 => frag0 x 3 6
  | 166 => frag1 x 3 6
  | 167 => frag0 x 3 7
  | 168 => frag1 x 3 7
  | 169 => x.limb 4 0 % 256
  | 170 => x.limb 4 1 % 256
  | 171 => x.limb 4 2 % 256
  | 172 => x.limb 4 3 % 256
  | 173 => frag0 x 4 0
  | 174 => frag1 x 4 0
  | 175 => frag0 x 4 1
  | 176 => frag1 x 4 1
  | 177 => frag0 x 4 2
  | 178 => frag1 x 4 2
  | 179 => frag0 x 4 3
  | 180 => frag1 x 4 3
  | 181 => frag0 x 4 4
  | 182 => frag1 x 4 4
  | 183 => frag0 x 4 5
  | 184 => frag1 x 4 5
  | 185 => frag0 x 4 6
  | 186 => frag1 x 4 6
  | 187 => frag0 x 4 7
  | 188 => frag1 x 4 7
  | 189 => x.previous 0
  | 190 => 0
  | 191 => x.previous 2
  | 192 => 0
  | 193 => x.previous 12
  | 194 => 0
  | 195 => x.previous 14
  | 196 => 0
  | _ => 0

/-- The row's assignment over the field. -/
def assignment {p : Nat} (x : RowInput) (i : Nat) : ZMod p := (column x i : ZMod p)

variable {p : Nat}

/-! The honest value of each column, by `rfl` (one lemma per column, for `simp only [honest_column]`). -/

@[honest_column] theorem assignment_0 : assignment (p := p) x 0 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_1 : assignment (p := p) x 1 = ((x.invocation : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_2 : assignment (p := p) x 2 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_3 : assignment (p := p) x 3 = ((x.control : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_4 : assignment (p := p) x 4 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_5 : assignment (p := p) x 5 = ((bump x.control : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_6 : assignment (p := p) x 6 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_7 : assignment (p := p) x 7 = ((slotNat x.call 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_8 : assignment (p := p) x 8 = ((slotNat x.call 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_9 : assignment (p := p) x 9 = ((slotNat x.call 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_10 : assignment (p := p) x 10 = ((slotNat x.call 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_11 : assignment (p := p) x 11 = ((slotNat x.call 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_12 : assignment (p := p) x 12 = ((slotNat x.call 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_13 : assignment (p := p) x 13 = ((slotNat x.call 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_14 : assignment (p := p) x 14 = (((x.read 1).lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_15 : assignment (p := p) x 15 = (((x.read 1).hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_16 : assignment (p := p) x 16 = ((x.limb 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_17 : assignment (p := p) x 17 = ((x.limb 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_18 : assignment (p := p) x 18 = ((out x 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_19 : assignment (p := p) x 19 = ((out x 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_20 : assignment (p := p) x 20 = ((x.limb 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_21 : assignment (p := p) x 21 = ((x.limb 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_22 : assignment (p := p) x 22 = ((out x 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_23 : assignment (p := p) x 23 = ((out x 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_24 : assignment (p := p) x 24 = ((x.limb 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_25 : assignment (p := p) x 25 = ((x.limb 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_26 : assignment (p := p) x 26 = ((out x 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_27 : assignment (p := p) x 27 = ((out x 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_28 : assignment (p := p) x 28 = ((x.limb 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_29 : assignment (p := p) x 29 = ((x.limb 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_30 : assignment (p := p) x 30 = ((out x 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_31 : assignment (p := p) x 31 = ((out x 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_32 : assignment (p := p) x 32 = ((x.limb 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_33 : assignment (p := p) x 33 = ((x.limb 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_34 : assignment (p := p) x 34 = ((out x 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_35 : assignment (p := p) x 35 = ((out x 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_36 : assignment (p := p) x 36 = ((x.limb 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_37 : assignment (p := p) x 37 = ((x.limb 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_38 : assignment (p := p) x 38 = ((out x 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_39 : assignment (p := p) x 39 = ((out x 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_40 : assignment (p := p) x 40 = ((x.limb 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_41 : assignment (p := p) x 41 = ((x.limb 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_42 : assignment (p := p) x 42 = ((out x 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_43 : assignment (p := p) x 43 = ((out x 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_44 : assignment (p := p) x 44 = ((x.limb 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_45 : assignment (p := p) x 45 = ((x.limb 3 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_46 : assignment (p := p) x 46 = ((out x 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_47 : assignment (p := p) x 47 = ((out x 3 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_48 : assignment (p := p) x 48 = ((x.limb 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_49 : assignment (p := p) x 49 = ((x.limb 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_50 : assignment (p := p) x 50 = ((out x 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_51 : assignment (p := p) x 51 = ((out x 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_52 : assignment (p := p) x 52 = ((x.limb 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_53 : assignment (p := p) x 53 = ((x.limb 4 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_54 : assignment (p := p) x 54 = ((out x 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_55 : assignment (p := p) x 55 = ((out x 4 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_56 : assignment (p := p) x 56 = ((x.limb 5 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_57 : assignment (p := p) x 57 = ((x.limb 5 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_58 : assignment (p := p) x 58 = ((x.limb 5 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_59 : assignment (p := p) x 59 = ((x.limb 5 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_60 : assignment (p := p) x 60 = ((x.limb 6 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_61 : assignment (p := p) x 61 = ((x.limb 6 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_62 : assignment (p := p) x 62 = ((x.limb 6 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_63 : assignment (p := p) x 63 = ((x.limb 6 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_64 : assignment (p := p) x 64 = ((x.limb 5 0 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_65 : assignment (p := p) x 65 = ((x.limb 5 1 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_66 : assignment (p := p) x 66 = ((x.limb 5 2 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_67 : assignment (p := p) x 67 = ((x.limb 5 3 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_68 : assignment (p := p) x 68 = ((top x 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_69 : assignment (p := p) x 69 = ((top x 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_70 : assignment (p := p) x 70 = ((top x 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_71 : assignment (p := p) x 71 = ((top x 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_72 : assignment (p := p) x 72 = ((rotLimb x 0 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_73 : assignment (p := p) x 73 = ((rotLimb x 1 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_74 : assignment (p := p) x 74 = ((rotLimb x 2 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_75 : assignment (p := p) x 75 = ((rotLimb x 3 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_76 : assignment (p := p) x 76 = ((d x 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_77 : assignment (p := p) x 77 = ((d x 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_78 : assignment (p := p) x 78 = ((d x 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_79 : assignment (p := p) x 79 = ((d x 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_80 : assignment (p := p) x 80 = ((d x 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_81 : assignment (p := p) x 81 = ((d x 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_82 : assignment (p := p) x 82 = ((d x 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_83 : assignment (p := p) x 83 = ((d x 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_84 : assignment (p := p) x 84 = ((flag x 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_85 : assignment (p := p) x 85 = ((flag x 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_86 : assignment (p := p) x 86 = ((flag x 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_87 : assignment (p := p) x 87 = ((flag x 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_88 : assignment (p := p) x 88 = ((flag x 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_89 : assignment (p := p) x 89 = ((x.limb 0 0 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_90 : assignment (p := p) x 90 = ((x.limb 0 1 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_91 : assignment (p := p) x 91 = ((x.limb 0 2 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_92 : assignment (p := p) x 92 = ((x.limb 0 3 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_93 : assignment (p := p) x 93 = ((frag0 x 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_94 : assignment (p := p) x 94 = ((frag1 x 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_95 : assignment (p := p) x 95 = ((frag0 x 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_96 : assignment (p := p) x 96 = ((frag1 x 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_97 : assignment (p := p) x 97 = ((frag0 x 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_98 : assignment (p := p) x 98 = ((frag1 x 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_99 : assignment (p := p) x 99 = ((frag0 x 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_100 : assignment (p := p) x 100 = ((frag1 x 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_101 : assignment (p := p) x 101 = ((frag0 x 0 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_102 : assignment (p := p) x 102 = ((frag1 x 0 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_103 : assignment (p := p) x 103 = ((frag0 x 0 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_104 : assignment (p := p) x 104 = ((frag1 x 0 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_105 : assignment (p := p) x 105 = ((frag0 x 0 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_106 : assignment (p := p) x 106 = ((frag1 x 0 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_107 : assignment (p := p) x 107 = ((frag0 x 0 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_108 : assignment (p := p) x 108 = ((frag1 x 0 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_109 : assignment (p := p) x 109 = ((x.limb 1 0 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_110 : assignment (p := p) x 110 = ((x.limb 1 1 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_111 : assignment (p := p) x 111 = ((x.limb 1 2 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_112 : assignment (p := p) x 112 = ((x.limb 1 3 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_113 : assignment (p := p) x 113 = ((frag0 x 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_114 : assignment (p := p) x 114 = ((frag1 x 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_115 : assignment (p := p) x 115 = ((frag0 x 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_116 : assignment (p := p) x 116 = ((frag1 x 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_117 : assignment (p := p) x 117 = ((frag0 x 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_118 : assignment (p := p) x 118 = ((frag1 x 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_119 : assignment (p := p) x 119 = ((frag0 x 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_120 : assignment (p := p) x 120 = ((frag1 x 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_121 : assignment (p := p) x 121 = ((frag0 x 1 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_122 : assignment (p := p) x 122 = ((frag1 x 1 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_123 : assignment (p := p) x 123 = ((frag0 x 1 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_124 : assignment (p := p) x 124 = ((frag1 x 1 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_125 : assignment (p := p) x 125 = ((frag0 x 1 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_126 : assignment (p := p) x 126 = ((frag1 x 1 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_127 : assignment (p := p) x 127 = ((frag0 x 1 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_128 : assignment (p := p) x 128 = ((frag1 x 1 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_129 : assignment (p := p) x 129 = ((x.limb 2 0 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_130 : assignment (p := p) x 130 = ((x.limb 2 1 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_131 : assignment (p := p) x 131 = ((x.limb 2 2 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_132 : assignment (p := p) x 132 = ((x.limb 2 3 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_133 : assignment (p := p) x 133 = ((frag0 x 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_134 : assignment (p := p) x 134 = ((frag1 x 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_135 : assignment (p := p) x 135 = ((frag0 x 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_136 : assignment (p := p) x 136 = ((frag1 x 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_137 : assignment (p := p) x 137 = ((frag0 x 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_138 : assignment (p := p) x 138 = ((frag1 x 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_139 : assignment (p := p) x 139 = ((frag0 x 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_140 : assignment (p := p) x 140 = ((frag1 x 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_141 : assignment (p := p) x 141 = ((frag0 x 2 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_142 : assignment (p := p) x 142 = ((frag1 x 2 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_143 : assignment (p := p) x 143 = ((frag0 x 2 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_144 : assignment (p := p) x 144 = ((frag1 x 2 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_145 : assignment (p := p) x 145 = ((frag0 x 2 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_146 : assignment (p := p) x 146 = ((frag1 x 2 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_147 : assignment (p := p) x 147 = ((frag0 x 2 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_148 : assignment (p := p) x 148 = ((frag1 x 2 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_149 : assignment (p := p) x 149 = ((x.limb 3 0 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_150 : assignment (p := p) x 150 = ((x.limb 3 1 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_151 : assignment (p := p) x 151 = ((x.limb 3 2 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_152 : assignment (p := p) x 152 = ((x.limb 3 3 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_153 : assignment (p := p) x 153 = ((frag0 x 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_154 : assignment (p := p) x 154 = ((frag1 x 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_155 : assignment (p := p) x 155 = ((frag0 x 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_156 : assignment (p := p) x 156 = ((frag1 x 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_157 : assignment (p := p) x 157 = ((frag0 x 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_158 : assignment (p := p) x 158 = ((frag1 x 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_159 : assignment (p := p) x 159 = ((frag0 x 3 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_160 : assignment (p := p) x 160 = ((frag1 x 3 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_161 : assignment (p := p) x 161 = ((frag0 x 3 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_162 : assignment (p := p) x 162 = ((frag1 x 3 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_163 : assignment (p := p) x 163 = ((frag0 x 3 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_164 : assignment (p := p) x 164 = ((frag1 x 3 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_165 : assignment (p := p) x 165 = ((frag0 x 3 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_166 : assignment (p := p) x 166 = ((frag1 x 3 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_167 : assignment (p := p) x 167 = ((frag0 x 3 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_168 : assignment (p := p) x 168 = ((frag1 x 3 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_169 : assignment (p := p) x 169 = ((x.limb 4 0 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_170 : assignment (p := p) x 170 = ((x.limb 4 1 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_171 : assignment (p := p) x 171 = ((x.limb 4 2 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_172 : assignment (p := p) x 172 = ((x.limb 4 3 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_173 : assignment (p := p) x 173 = ((frag0 x 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_174 : assignment (p := p) x 174 = ((frag1 x 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_175 : assignment (p := p) x 175 = ((frag0 x 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_176 : assignment (p := p) x 176 = ((frag1 x 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_177 : assignment (p := p) x 177 = ((frag0 x 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_178 : assignment (p := p) x 178 = ((frag1 x 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_179 : assignment (p := p) x 179 = ((frag0 x 4 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_180 : assignment (p := p) x 180 = ((frag1 x 4 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_181 : assignment (p := p) x 181 = ((frag0 x 4 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_182 : assignment (p := p) x 182 = ((frag1 x 4 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_183 : assignment (p := p) x 183 = ((frag0 x 4 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_184 : assignment (p := p) x 184 = ((frag1 x 4 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_185 : assignment (p := p) x 185 = ((frag0 x 4 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_186 : assignment (p := p) x 186 = ((frag1 x 4 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_187 : assignment (p := p) x 187 = ((frag0 x 4 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_188 : assignment (p := p) x 188 = ((frag1 x 4 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_189 : assignment (p := p) x 189 = ((x.previous 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_190 : assignment (p := p) x 190 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_191 : assignment (p := p) x 191 = ((x.previous 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_192 : assignment (p := p) x 192 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_193 : assignment (p := p) x 193 = ((x.previous 12 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_194 : assignment (p := p) x 194 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_195 : assignment (p := p) x 195 = ((x.previous 14 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_196 : assignment (p := p) x 196 = ((0 : Nat) : ZMod p) := rfl

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
