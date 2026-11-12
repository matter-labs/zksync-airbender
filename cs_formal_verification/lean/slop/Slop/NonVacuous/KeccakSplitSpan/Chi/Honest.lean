module
public import Slop.NonVacuous.KeccakSplitSpan.Common

@[expose] public section

/-! The honest assignment of one chi row (`Chi5.importedConstraints`' columns, numbered as the artifact numbers
    them), computed from the row's inputs: every nibble of every written lane is chi of the read nibbles. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Chi
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

variable (x : RowInput)

/-- The call's plane `y`. -/
def plane : Nat := x.call % 5

/-- Nibble `n` (0 to 15) of the read lane `i`. -/
def inNib (i n : Nat) : Nat := nib (x.limb i (n / 4)) (n % 4)

/-- Nibble `n` of the written lane `i`: chi on four bits. -/
def chiNib (i n : Nat) : Nat :=
  inNib x i n ^^^ ((15 ^^^ inNib x ((i + 1) % 5) n) &&& inNib x ((i + 2) % 5) n)

/-- Limb `m` of the written lane `i`. -/
def out (i m : Nat) : Nat :=
  chiNib x i (4 * m) + 16 * chiNib x i (4 * m + 1) + 256 * chiNib x i (4 * m + 2) + 4096 * chiNib x i (4 * m + 3)

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
  | 12 => (x.read 1).lo
  | 13 => (x.read 1).hi
  | 14 => x.limb 0 0
  | 15 => x.limb 0 1
  | 16 => out x 0 0
  | 17 => out x 0 1
  | 18 => x.limb 0 2
  | 19 => x.limb 0 3
  | 20 => out x 0 2
  | 21 => out x 0 3
  | 22 => x.limb 1 0
  | 23 => x.limb 1 1
  | 24 => out x 1 0
  | 25 => out x 1 1
  | 26 => x.limb 1 2
  | 27 => x.limb 1 3
  | 28 => out x 1 2
  | 29 => out x 1 3
  | 30 => x.limb 2 0
  | 31 => x.limb 2 1
  | 32 => out x 2 0
  | 33 => out x 2 1
  | 34 => x.limb 2 2
  | 35 => x.limb 2 3
  | 36 => out x 2 2
  | 37 => out x 2 3
  | 38 => x.limb 3 0
  | 39 => x.limb 3 1
  | 40 => out x 3 0
  | 41 => out x 3 1
  | 42 => x.limb 3 2
  | 43 => x.limb 3 3
  | 44 => out x 3 2
  | 45 => out x 3 3
  | 46 => x.limb 4 0
  | 47 => x.limb 4 1
  | 48 => out x 4 0
  | 49 => out x 4 1
  | 50 => x.limb 4 2
  | 51 => x.limb 4 3
  | 52 => out x 4 2
  | 53 => out x 4 3
  | 54 => plane x
  | 55 => nib (x.limb 0 0) 0
  | 56 => nib (x.limb 0 0) 1
  | 57 => nib (x.limb 0 0) 2
  | 58 => nib (x.limb 0 1) 0
  | 59 => nib (x.limb 0 1) 1
  | 60 => nib (x.limb 0 1) 2
  | 61 => nib (x.limb 0 2) 0
  | 62 => nib (x.limb 0 2) 1
  | 63 => nib (x.limb 0 2) 2
  | 64 => nib (x.limb 0 3) 0
  | 65 => nib (x.limb 0 3) 1
  | 66 => nib (x.limb 0 3) 2
  | 67 => nib (x.limb 1 0) 0
  | 68 => nib (x.limb 1 0) 1
  | 69 => nib (x.limb 1 0) 2
  | 70 => nib (x.limb 1 1) 0
  | 71 => nib (x.limb 1 1) 1
  | 72 => nib (x.limb 1 1) 2
  | 73 => nib (x.limb 1 2) 0
  | 74 => nib (x.limb 1 2) 1
  | 75 => nib (x.limb 1 2) 2
  | 76 => nib (x.limb 1 3) 0
  | 77 => nib (x.limb 1 3) 1
  | 78 => nib (x.limb 1 3) 2
  | 79 => nib (x.limb 2 0) 0
  | 80 => nib (x.limb 2 0) 1
  | 81 => nib (x.limb 2 0) 2
  | 82 => nib (x.limb 2 1) 0
  | 83 => nib (x.limb 2 1) 1
  | 84 => nib (x.limb 2 1) 2
  | 85 => nib (x.limb 2 2) 0
  | 86 => nib (x.limb 2 2) 1
  | 87 => nib (x.limb 2 2) 2
  | 88 => nib (x.limb 2 3) 0
  | 89 => nib (x.limb 2 3) 1
  | 90 => nib (x.limb 2 3) 2
  | 91 => nib (x.limb 3 0) 0
  | 92 => nib (x.limb 3 0) 1
  | 93 => nib (x.limb 3 0) 2
  | 94 => nib (x.limb 3 1) 0
  | 95 => nib (x.limb 3 1) 1
  | 96 => nib (x.limb 3 1) 2
  | 97 => nib (x.limb 3 2) 0
  | 98 => nib (x.limb 3 2) 1
  | 99 => nib (x.limb 3 2) 2
  | 100 => nib (x.limb 3 3) 0
  | 101 => nib (x.limb 3 3) 1
  | 102 => nib (x.limb 3 3) 2
  | 103 => nib (x.limb 4 0) 0
  | 104 => nib (x.limb 4 0) 1
  | 105 => nib (x.limb 4 0) 2
  | 106 => nib (x.limb 4 1) 0
  | 107 => nib (x.limb 4 1) 1
  | 108 => nib (x.limb 4 1) 2
  | 109 => nib (x.limb 4 2) 0
  | 110 => nib (x.limb 4 2) 1
  | 111 => nib (x.limb 4 2) 2
  | 112 => nib (x.limb 4 3) 0
  | 113 => nib (x.limb 4 3) 1
  | 114 => nib (x.limb 4 3) 2
  | 115 => chiNib x 0 0
  | 116 => chiNib x 0 1
  | 117 => chiNib x 0 2
  | 118 => chiNib x 0 4
  | 119 => chiNib x 0 5
  | 120 => chiNib x 0 6
  | 121 => chiNib x 0 8
  | 122 => chiNib x 0 9
  | 123 => chiNib x 0 10
  | 124 => chiNib x 0 12
  | 125 => chiNib x 0 13
  | 126 => chiNib x 0 14
  | 127 => chiNib x 1 0
  | 128 => chiNib x 1 1
  | 129 => chiNib x 1 2
  | 130 => chiNib x 1 4
  | 131 => chiNib x 1 5
  | 132 => chiNib x 1 6
  | 133 => chiNib x 1 8
  | 134 => chiNib x 1 9
  | 135 => chiNib x 1 10
  | 136 => chiNib x 1 12
  | 137 => chiNib x 1 13
  | 138 => chiNib x 1 14
  | 139 => chiNib x 2 0
  | 140 => chiNib x 2 1
  | 141 => chiNib x 2 2
  | 142 => chiNib x 2 4
  | 143 => chiNib x 2 5
  | 144 => chiNib x 2 6
  | 145 => chiNib x 2 8
  | 146 => chiNib x 2 9
  | 147 => chiNib x 2 10
  | 148 => chiNib x 2 12
  | 149 => chiNib x 2 13
  | 150 => chiNib x 2 14
  | 151 => chiNib x 3 0
  | 152 => chiNib x 3 1
  | 153 => chiNib x 3 2
  | 154 => chiNib x 3 4
  | 155 => chiNib x 3 5
  | 156 => chiNib x 3 6
  | 157 => chiNib x 3 8
  | 158 => chiNib x 3 9
  | 159 => chiNib x 3 10
  | 160 => chiNib x 3 12
  | 161 => chiNib x 3 13
  | 162 => chiNib x 3 14
  | 163 => chiNib x 4 0
  | 164 => chiNib x 4 1
  | 165 => chiNib x 4 2
  | 166 => chiNib x 4 4
  | 167 => chiNib x 4 5
  | 168 => chiNib x 4 6
  | 169 => chiNib x 4 8
  | 170 => chiNib x 4 9
  | 171 => chiNib x 4 10
  | 172 => chiNib x 4 12
  | 173 => chiNib x 4 13
  | 174 => chiNib x 4 14
  | 175 => x.previous 0
  | 176 => 0
  | 177 => x.previous 2
  | 178 => 0
  | 179 => x.previous 4
  | 180 => 0
  | 181 => x.previous 6
  | 182 => 0
  | 183 => x.previous 8
  | 184 => 0
  | 185 => x.previous 10
  | 186 => 0
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
@[honest_column] theorem assignment_12 : assignment (p := p) x 12 = (((x.read 1).lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_13 : assignment (p := p) x 13 = (((x.read 1).hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_14 : assignment (p := p) x 14 = ((x.limb 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_15 : assignment (p := p) x 15 = ((x.limb 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_16 : assignment (p := p) x 16 = ((out x 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_17 : assignment (p := p) x 17 = ((out x 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_18 : assignment (p := p) x 18 = ((x.limb 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_19 : assignment (p := p) x 19 = ((x.limb 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_20 : assignment (p := p) x 20 = ((out x 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_21 : assignment (p := p) x 21 = ((out x 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_22 : assignment (p := p) x 22 = ((x.limb 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_23 : assignment (p := p) x 23 = ((x.limb 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_24 : assignment (p := p) x 24 = ((out x 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_25 : assignment (p := p) x 25 = ((out x 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_26 : assignment (p := p) x 26 = ((x.limb 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_27 : assignment (p := p) x 27 = ((x.limb 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_28 : assignment (p := p) x 28 = ((out x 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_29 : assignment (p := p) x 29 = ((out x 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_30 : assignment (p := p) x 30 = ((x.limb 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_31 : assignment (p := p) x 31 = ((x.limb 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_32 : assignment (p := p) x 32 = ((out x 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_33 : assignment (p := p) x 33 = ((out x 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_34 : assignment (p := p) x 34 = ((x.limb 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_35 : assignment (p := p) x 35 = ((x.limb 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_36 : assignment (p := p) x 36 = ((out x 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_37 : assignment (p := p) x 37 = ((out x 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_38 : assignment (p := p) x 38 = ((x.limb 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_39 : assignment (p := p) x 39 = ((x.limb 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_40 : assignment (p := p) x 40 = ((out x 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_41 : assignment (p := p) x 41 = ((out x 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_42 : assignment (p := p) x 42 = ((x.limb 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_43 : assignment (p := p) x 43 = ((x.limb 3 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_44 : assignment (p := p) x 44 = ((out x 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_45 : assignment (p := p) x 45 = ((out x 3 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_46 : assignment (p := p) x 46 = ((x.limb 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_47 : assignment (p := p) x 47 = ((x.limb 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_48 : assignment (p := p) x 48 = ((out x 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_49 : assignment (p := p) x 49 = ((out x 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_50 : assignment (p := p) x 50 = ((x.limb 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_51 : assignment (p := p) x 51 = ((x.limb 4 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_52 : assignment (p := p) x 52 = ((out x 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_53 : assignment (p := p) x 53 = ((out x 4 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_54 : assignment (p := p) x 54 = ((plane x : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_55 : assignment (p := p) x 55 = ((nib (x.limb 0 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_56 : assignment (p := p) x 56 = ((nib (x.limb 0 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_57 : assignment (p := p) x 57 = ((nib (x.limb 0 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_58 : assignment (p := p) x 58 = ((nib (x.limb 0 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_59 : assignment (p := p) x 59 = ((nib (x.limb 0 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_60 : assignment (p := p) x 60 = ((nib (x.limb 0 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_61 : assignment (p := p) x 61 = ((nib (x.limb 0 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_62 : assignment (p := p) x 62 = ((nib (x.limb 0 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_63 : assignment (p := p) x 63 = ((nib (x.limb 0 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_64 : assignment (p := p) x 64 = ((nib (x.limb 0 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_65 : assignment (p := p) x 65 = ((nib (x.limb 0 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_66 : assignment (p := p) x 66 = ((nib (x.limb 0 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_67 : assignment (p := p) x 67 = ((nib (x.limb 1 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_68 : assignment (p := p) x 68 = ((nib (x.limb 1 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_69 : assignment (p := p) x 69 = ((nib (x.limb 1 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_70 : assignment (p := p) x 70 = ((nib (x.limb 1 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_71 : assignment (p := p) x 71 = ((nib (x.limb 1 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_72 : assignment (p := p) x 72 = ((nib (x.limb 1 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_73 : assignment (p := p) x 73 = ((nib (x.limb 1 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_74 : assignment (p := p) x 74 = ((nib (x.limb 1 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_75 : assignment (p := p) x 75 = ((nib (x.limb 1 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_76 : assignment (p := p) x 76 = ((nib (x.limb 1 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_77 : assignment (p := p) x 77 = ((nib (x.limb 1 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_78 : assignment (p := p) x 78 = ((nib (x.limb 1 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_79 : assignment (p := p) x 79 = ((nib (x.limb 2 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_80 : assignment (p := p) x 80 = ((nib (x.limb 2 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_81 : assignment (p := p) x 81 = ((nib (x.limb 2 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_82 : assignment (p := p) x 82 = ((nib (x.limb 2 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_83 : assignment (p := p) x 83 = ((nib (x.limb 2 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_84 : assignment (p := p) x 84 = ((nib (x.limb 2 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_85 : assignment (p := p) x 85 = ((nib (x.limb 2 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_86 : assignment (p := p) x 86 = ((nib (x.limb 2 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_87 : assignment (p := p) x 87 = ((nib (x.limb 2 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_88 : assignment (p := p) x 88 = ((nib (x.limb 2 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_89 : assignment (p := p) x 89 = ((nib (x.limb 2 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_90 : assignment (p := p) x 90 = ((nib (x.limb 2 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_91 : assignment (p := p) x 91 = ((nib (x.limb 3 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_92 : assignment (p := p) x 92 = ((nib (x.limb 3 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_93 : assignment (p := p) x 93 = ((nib (x.limb 3 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_94 : assignment (p := p) x 94 = ((nib (x.limb 3 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_95 : assignment (p := p) x 95 = ((nib (x.limb 3 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_96 : assignment (p := p) x 96 = ((nib (x.limb 3 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_97 : assignment (p := p) x 97 = ((nib (x.limb 3 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_98 : assignment (p := p) x 98 = ((nib (x.limb 3 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_99 : assignment (p := p) x 99 = ((nib (x.limb 3 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_100 : assignment (p := p) x 100 = ((nib (x.limb 3 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_101 : assignment (p := p) x 101 = ((nib (x.limb 3 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_102 : assignment (p := p) x 102 = ((nib (x.limb 3 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_103 : assignment (p := p) x 103 = ((nib (x.limb 4 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_104 : assignment (p := p) x 104 = ((nib (x.limb 4 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_105 : assignment (p := p) x 105 = ((nib (x.limb 4 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_106 : assignment (p := p) x 106 = ((nib (x.limb 4 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_107 : assignment (p := p) x 107 = ((nib (x.limb 4 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_108 : assignment (p := p) x 108 = ((nib (x.limb 4 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_109 : assignment (p := p) x 109 = ((nib (x.limb 4 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_110 : assignment (p := p) x 110 = ((nib (x.limb 4 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_111 : assignment (p := p) x 111 = ((nib (x.limb 4 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_112 : assignment (p := p) x 112 = ((nib (x.limb 4 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_113 : assignment (p := p) x 113 = ((nib (x.limb 4 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_114 : assignment (p := p) x 114 = ((nib (x.limb 4 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_115 : assignment (p := p) x 115 = ((chiNib x 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_116 : assignment (p := p) x 116 = ((chiNib x 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_117 : assignment (p := p) x 117 = ((chiNib x 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_118 : assignment (p := p) x 118 = ((chiNib x 0 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_119 : assignment (p := p) x 119 = ((chiNib x 0 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_120 : assignment (p := p) x 120 = ((chiNib x 0 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_121 : assignment (p := p) x 121 = ((chiNib x 0 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_122 : assignment (p := p) x 122 = ((chiNib x 0 9 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_123 : assignment (p := p) x 123 = ((chiNib x 0 10 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_124 : assignment (p := p) x 124 = ((chiNib x 0 12 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_125 : assignment (p := p) x 125 = ((chiNib x 0 13 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_126 : assignment (p := p) x 126 = ((chiNib x 0 14 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_127 : assignment (p := p) x 127 = ((chiNib x 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_128 : assignment (p := p) x 128 = ((chiNib x 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_129 : assignment (p := p) x 129 = ((chiNib x 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_130 : assignment (p := p) x 130 = ((chiNib x 1 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_131 : assignment (p := p) x 131 = ((chiNib x 1 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_132 : assignment (p := p) x 132 = ((chiNib x 1 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_133 : assignment (p := p) x 133 = ((chiNib x 1 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_134 : assignment (p := p) x 134 = ((chiNib x 1 9 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_135 : assignment (p := p) x 135 = ((chiNib x 1 10 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_136 : assignment (p := p) x 136 = ((chiNib x 1 12 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_137 : assignment (p := p) x 137 = ((chiNib x 1 13 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_138 : assignment (p := p) x 138 = ((chiNib x 1 14 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_139 : assignment (p := p) x 139 = ((chiNib x 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_140 : assignment (p := p) x 140 = ((chiNib x 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_141 : assignment (p := p) x 141 = ((chiNib x 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_142 : assignment (p := p) x 142 = ((chiNib x 2 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_143 : assignment (p := p) x 143 = ((chiNib x 2 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_144 : assignment (p := p) x 144 = ((chiNib x 2 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_145 : assignment (p := p) x 145 = ((chiNib x 2 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_146 : assignment (p := p) x 146 = ((chiNib x 2 9 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_147 : assignment (p := p) x 147 = ((chiNib x 2 10 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_148 : assignment (p := p) x 148 = ((chiNib x 2 12 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_149 : assignment (p := p) x 149 = ((chiNib x 2 13 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_150 : assignment (p := p) x 150 = ((chiNib x 2 14 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_151 : assignment (p := p) x 151 = ((chiNib x 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_152 : assignment (p := p) x 152 = ((chiNib x 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_153 : assignment (p := p) x 153 = ((chiNib x 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_154 : assignment (p := p) x 154 = ((chiNib x 3 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_155 : assignment (p := p) x 155 = ((chiNib x 3 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_156 : assignment (p := p) x 156 = ((chiNib x 3 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_157 : assignment (p := p) x 157 = ((chiNib x 3 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_158 : assignment (p := p) x 158 = ((chiNib x 3 9 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_159 : assignment (p := p) x 159 = ((chiNib x 3 10 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_160 : assignment (p := p) x 160 = ((chiNib x 3 12 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_161 : assignment (p := p) x 161 = ((chiNib x 3 13 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_162 : assignment (p := p) x 162 = ((chiNib x 3 14 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_163 : assignment (p := p) x 163 = ((chiNib x 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_164 : assignment (p := p) x 164 = ((chiNib x 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_165 : assignment (p := p) x 165 = ((chiNib x 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_166 : assignment (p := p) x 166 = ((chiNib x 4 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_167 : assignment (p := p) x 167 = ((chiNib x 4 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_168 : assignment (p := p) x 168 = ((chiNib x 4 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_169 : assignment (p := p) x 169 = ((chiNib x 4 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_170 : assignment (p := p) x 170 = ((chiNib x 4 9 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_171 : assignment (p := p) x 171 = ((chiNib x 4 10 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_172 : assignment (p := p) x 172 = ((chiNib x 4 12 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_173 : assignment (p := p) x 173 = ((chiNib x 4 13 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_174 : assignment (p := p) x 174 = ((chiNib x 4 14 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_175 : assignment (p := p) x 175 = ((x.previous 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_176 : assignment (p := p) x 176 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_177 : assignment (p := p) x 177 = ((x.previous 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_178 : assignment (p := p) x 178 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_179 : assignment (p := p) x 179 = ((x.previous 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_180 : assignment (p := p) x 180 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_181 : assignment (p := p) x 181 = ((x.previous 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_182 : assignment (p := p) x 182 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_183 : assignment (p := p) x 183 = ((x.previous 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_184 : assignment (p := p) x 184 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_185 : assignment (p := p) x 185 = ((x.previous 10 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_186 : assignment (p := p) x 186 = ((0 : Nat) : ZMod p) := rfl

end Airbender.NonVacuous.KeccakSplitSpan.Chi
