module
public import Proven.NonVacuous.KeccakSplitSpan.Common

@[expose] public section

/-! The honest assignment of one column-parity row (`ColumnParity.importedConstraints`' columns, numbered as the
    artifact numbers them), computed from the row's inputs: the first lane gets iota on its iota bytes (0, 1, 3, 7),
    the parity is the nibble-wise XOR of the five lanes, and every byte and nibble split is the honest one. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Parity
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

variable (x : RowInput)

/-- The iota round the control row selects: the call's round on the first call of a round, else zero. -/
def round : Nat := if x.call % 5 = 0 then x.call / 15 else 0

/-- Limb `m` of the written first lane: its iota bytes XORed with the round-constant bytes, the others kept. -/
def out (m : Nat) : Nat :=
  match m with
  | 0 => (x.limb 0 0 % 256 ^^^ rcByte (round x)) + 256 * (x.limb 0 0 / 256 ^^^ rcByte (round x + 32))
  | 1 => x.limb 0 1 % 256 + 256 * (x.limb 0 1 / 256 ^^^ rcByte (round x + 96))
  | 2 => x.limb 0 2
  | _ => x.limb 0 3 % 256 + 256 * (x.limb 0 3 / 256 ^^^ rcByte (round x + 224))

/-- Nibble `j` of parity limb `m`: the XOR of the five lanes' nibbles. -/
def parityNib (m j : Nat) : Nat :=
  nib (out x m) j ^^^ nib (x.limb 1 m) j ^^^ nib (x.limb 2 m) j ^^^ nib (x.limb 3 m) j ^^^ nib (x.limb 4 m) j

/-- Parity limb `m`. -/
def parity (m : Nat) : Nat :=
  parityNib x m 0 + 16 * parityNib x m 1 + 256 * parityNib x m 2 + 4096 * parityNib x m 3

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
  | 13 => (x.read 1).lo
  | 14 => (x.read 1).hi
  | 15 => x.limb 0 0
  | 16 => x.limb 0 1
  | 17 => out x 0
  | 18 => out x 1
  | 19 => x.limb 0 2
  | 20 => x.limb 0 3
  | 21 => out x 2
  | 22 => out x 3
  | 23 => x.limb 1 0
  | 24 => x.limb 1 1
  | 25 => x.limb 1 2
  | 26 => x.limb 1 3
  | 27 => x.limb 2 0
  | 28 => x.limb 2 1
  | 29 => x.limb 2 2
  | 30 => x.limb 2 3
  | 31 => x.limb 3 0
  | 32 => x.limb 3 1
  | 33 => x.limb 3 2
  | 34 => x.limb 3 3
  | 35 => x.limb 4 0
  | 36 => x.limb 4 1
  | 37 => x.limb 4 2
  | 38 => x.limb 4 3
  | 39 => x.limb 5 0
  | 40 => x.limb 5 1
  | 41 => parity x 0
  | 42 => parity x 1
  | 43 => x.limb 5 2
  | 44 => x.limb 5 3
  | 45 => parity x 2
  | 46 => parity x 3
  | 47 => round x
  | 48 => x.limb 0 0 % 256
  | 49 => x.limb 0 1 % 256
  | 50 => x.limb 0 3 % 256
  | 51 => nib (out x 0) 0
  | 52 => nib (out x 0) 1
  | 53 => nib (out x 0) 2
  | 54 => nib (out x 1) 0
  | 55 => nib (out x 1) 1
  | 56 => nib (out x 1) 2
  | 57 => nib (out x 2) 0
  | 58 => nib (out x 2) 1
  | 59 => nib (out x 2) 2
  | 60 => nib (out x 3) 0
  | 61 => nib (out x 3) 1
  | 62 => nib (out x 3) 2
  | 63 => nib (x.limb 1 0) 0
  | 64 => nib (x.limb 1 0) 1
  | 65 => nib (x.limb 1 0) 2
  | 66 => nib (x.limb 1 1) 0
  | 67 => nib (x.limb 1 1) 1
  | 68 => nib (x.limb 1 1) 2
  | 69 => nib (x.limb 1 2) 0
  | 70 => nib (x.limb 1 2) 1
  | 71 => nib (x.limb 1 2) 2
  | 72 => nib (x.limb 1 3) 0
  | 73 => nib (x.limb 1 3) 1
  | 74 => nib (x.limb 1 3) 2
  | 75 => nib (x.limb 2 0) 0
  | 76 => nib (x.limb 2 0) 1
  | 77 => nib (x.limb 2 0) 2
  | 78 => nib (x.limb 2 1) 0
  | 79 => nib (x.limb 2 1) 1
  | 80 => nib (x.limb 2 1) 2
  | 81 => nib (x.limb 2 2) 0
  | 82 => nib (x.limb 2 2) 1
  | 83 => nib (x.limb 2 2) 2
  | 84 => nib (x.limb 2 3) 0
  | 85 => nib (x.limb 2 3) 1
  | 86 => nib (x.limb 2 3) 2
  | 87 => nib (x.limb 3 0) 0
  | 88 => nib (x.limb 3 0) 1
  | 89 => nib (x.limb 3 0) 2
  | 90 => nib (x.limb 3 1) 0
  | 91 => nib (x.limb 3 1) 1
  | 92 => nib (x.limb 3 1) 2
  | 93 => nib (x.limb 3 2) 0
  | 94 => nib (x.limb 3 2) 1
  | 95 => nib (x.limb 3 2) 2
  | 96 => nib (x.limb 3 3) 0
  | 97 => nib (x.limb 3 3) 1
  | 98 => nib (x.limb 3 3) 2
  | 99 => nib (x.limb 4 0) 0
  | 100 => nib (x.limb 4 0) 1
  | 101 => nib (x.limb 4 0) 2
  | 102 => nib (x.limb 4 1) 0
  | 103 => nib (x.limb 4 1) 1
  | 104 => nib (x.limb 4 1) 2
  | 105 => nib (x.limb 4 2) 0
  | 106 => nib (x.limb 4 2) 1
  | 107 => nib (x.limb 4 2) 2
  | 108 => nib (x.limb 4 3) 0
  | 109 => nib (x.limb 4 3) 1
  | 110 => nib (x.limb 4 3) 2
  | 111 => parityNib x 0 0
  | 112 => parityNib x 0 1
  | 113 => parityNib x 0 2
  | 114 => parityNib x 1 0
  | 115 => parityNib x 1 1
  | 116 => parityNib x 1 2
  | 117 => parityNib x 2 0
  | 118 => parityNib x 2 1
  | 119 => parityNib x 2 2
  | 120 => parityNib x 3 0
  | 121 => parityNib x 3 1
  | 122 => parityNib x 3 2
  | 123 => x.previous 0
  | 124 => 0
  | 125 => 1
  | 126 => x.previous 1
  | 127 => 0
  | 128 => 1
  | 129 => x.previous 2
  | 130 => 0
  | 131 => 1
  | 132 => x.previous 3
  | 133 => 0
  | 134 => 1
  | 135 => x.previous 4
  | 136 => 0
  | 137 => 1
  | 138 => x.previous 5
  | 139 => 0
  | 140 => 1
  | 141 => x.previous 6
  | 142 => 0
  | 143 => 1
  | 144 => x.previous 7
  | 145 => 0
  | 146 => 1
  | 147 => x.previous 8
  | 148 => 0
  | 149 => 1
  | 150 => x.previous 9
  | 151 => 0
  | 152 => 1
  | 153 => x.previous 10
  | 154 => 0
  | 155 => 1
  | 156 => x.previous 11
  | 157 => 0
  | 158 => 1
  | 159 => x.previous 12
  | 160 => 0
  | 161 => 1
  | 162 => x.previous 13
  | 163 => 0
  | 164 => 1
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
@[honest_column] theorem assignment_13 : assignment (p := p) x 13 = (((x.read 1).lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_14 : assignment (p := p) x 14 = (((x.read 1).hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_15 : assignment (p := p) x 15 = ((x.limb 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_16 : assignment (p := p) x 16 = ((x.limb 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_17 : assignment (p := p) x 17 = ((out x 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_18 : assignment (p := p) x 18 = ((out x 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_19 : assignment (p := p) x 19 = ((x.limb 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_20 : assignment (p := p) x 20 = ((x.limb 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_21 : assignment (p := p) x 21 = ((out x 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_22 : assignment (p := p) x 22 = ((out x 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_23 : assignment (p := p) x 23 = ((x.limb 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_24 : assignment (p := p) x 24 = ((x.limb 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_25 : assignment (p := p) x 25 = ((x.limb 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_26 : assignment (p := p) x 26 = ((x.limb 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_27 : assignment (p := p) x 27 = ((x.limb 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_28 : assignment (p := p) x 28 = ((x.limb 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_29 : assignment (p := p) x 29 = ((x.limb 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_30 : assignment (p := p) x 30 = ((x.limb 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_31 : assignment (p := p) x 31 = ((x.limb 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_32 : assignment (p := p) x 32 = ((x.limb 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_33 : assignment (p := p) x 33 = ((x.limb 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_34 : assignment (p := p) x 34 = ((x.limb 3 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_35 : assignment (p := p) x 35 = ((x.limb 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_36 : assignment (p := p) x 36 = ((x.limb 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_37 : assignment (p := p) x 37 = ((x.limb 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_38 : assignment (p := p) x 38 = ((x.limb 4 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_39 : assignment (p := p) x 39 = ((x.limb 5 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_40 : assignment (p := p) x 40 = ((x.limb 5 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_41 : assignment (p := p) x 41 = ((parity x 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_42 : assignment (p := p) x 42 = ((parity x 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_43 : assignment (p := p) x 43 = ((x.limb 5 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_44 : assignment (p := p) x 44 = ((x.limb 5 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_45 : assignment (p := p) x 45 = ((parity x 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_46 : assignment (p := p) x 46 = ((parity x 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_47 : assignment (p := p) x 47 = ((round x : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_48 : assignment (p := p) x 48 = ((x.limb 0 0 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_49 : assignment (p := p) x 49 = ((x.limb 0 1 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_50 : assignment (p := p) x 50 = ((x.limb 0 3 % 256 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_51 : assignment (p := p) x 51 = ((nib (out x 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_52 : assignment (p := p) x 52 = ((nib (out x 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_53 : assignment (p := p) x 53 = ((nib (out x 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_54 : assignment (p := p) x 54 = ((nib (out x 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_55 : assignment (p := p) x 55 = ((nib (out x 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_56 : assignment (p := p) x 56 = ((nib (out x 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_57 : assignment (p := p) x 57 = ((nib (out x 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_58 : assignment (p := p) x 58 = ((nib (out x 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_59 : assignment (p := p) x 59 = ((nib (out x 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_60 : assignment (p := p) x 60 = ((nib (out x 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_61 : assignment (p := p) x 61 = ((nib (out x 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_62 : assignment (p := p) x 62 = ((nib (out x 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_63 : assignment (p := p) x 63 = ((nib (x.limb 1 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_64 : assignment (p := p) x 64 = ((nib (x.limb 1 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_65 : assignment (p := p) x 65 = ((nib (x.limb 1 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_66 : assignment (p := p) x 66 = ((nib (x.limb 1 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_67 : assignment (p := p) x 67 = ((nib (x.limb 1 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_68 : assignment (p := p) x 68 = ((nib (x.limb 1 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_69 : assignment (p := p) x 69 = ((nib (x.limb 1 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_70 : assignment (p := p) x 70 = ((nib (x.limb 1 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_71 : assignment (p := p) x 71 = ((nib (x.limb 1 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_72 : assignment (p := p) x 72 = ((nib (x.limb 1 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_73 : assignment (p := p) x 73 = ((nib (x.limb 1 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_74 : assignment (p := p) x 74 = ((nib (x.limb 1 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_75 : assignment (p := p) x 75 = ((nib (x.limb 2 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_76 : assignment (p := p) x 76 = ((nib (x.limb 2 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_77 : assignment (p := p) x 77 = ((nib (x.limb 2 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_78 : assignment (p := p) x 78 = ((nib (x.limb 2 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_79 : assignment (p := p) x 79 = ((nib (x.limb 2 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_80 : assignment (p := p) x 80 = ((nib (x.limb 2 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_81 : assignment (p := p) x 81 = ((nib (x.limb 2 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_82 : assignment (p := p) x 82 = ((nib (x.limb 2 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_83 : assignment (p := p) x 83 = ((nib (x.limb 2 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_84 : assignment (p := p) x 84 = ((nib (x.limb 2 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_85 : assignment (p := p) x 85 = ((nib (x.limb 2 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_86 : assignment (p := p) x 86 = ((nib (x.limb 2 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_87 : assignment (p := p) x 87 = ((nib (x.limb 3 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_88 : assignment (p := p) x 88 = ((nib (x.limb 3 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_89 : assignment (p := p) x 89 = ((nib (x.limb 3 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_90 : assignment (p := p) x 90 = ((nib (x.limb 3 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_91 : assignment (p := p) x 91 = ((nib (x.limb 3 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_92 : assignment (p := p) x 92 = ((nib (x.limb 3 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_93 : assignment (p := p) x 93 = ((nib (x.limb 3 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_94 : assignment (p := p) x 94 = ((nib (x.limb 3 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_95 : assignment (p := p) x 95 = ((nib (x.limb 3 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_96 : assignment (p := p) x 96 = ((nib (x.limb 3 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_97 : assignment (p := p) x 97 = ((nib (x.limb 3 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_98 : assignment (p := p) x 98 = ((nib (x.limb 3 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_99 : assignment (p := p) x 99 = ((nib (x.limb 4 0) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_100 : assignment (p := p) x 100 = ((nib (x.limb 4 0) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_101 : assignment (p := p) x 101 = ((nib (x.limb 4 0) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_102 : assignment (p := p) x 102 = ((nib (x.limb 4 1) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_103 : assignment (p := p) x 103 = ((nib (x.limb 4 1) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_104 : assignment (p := p) x 104 = ((nib (x.limb 4 1) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_105 : assignment (p := p) x 105 = ((nib (x.limb 4 2) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_106 : assignment (p := p) x 106 = ((nib (x.limb 4 2) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_107 : assignment (p := p) x 107 = ((nib (x.limb 4 2) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_108 : assignment (p := p) x 108 = ((nib (x.limb 4 3) 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_109 : assignment (p := p) x 109 = ((nib (x.limb 4 3) 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_110 : assignment (p := p) x 110 = ((nib (x.limb 4 3) 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_111 : assignment (p := p) x 111 = ((parityNib x 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_112 : assignment (p := p) x 112 = ((parityNib x 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_113 : assignment (p := p) x 113 = ((parityNib x 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_114 : assignment (p := p) x 114 = ((parityNib x 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_115 : assignment (p := p) x 115 = ((parityNib x 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_116 : assignment (p := p) x 116 = ((parityNib x 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_117 : assignment (p := p) x 117 = ((parityNib x 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_118 : assignment (p := p) x 118 = ((parityNib x 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_119 : assignment (p := p) x 119 = ((parityNib x 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_120 : assignment (p := p) x 120 = ((parityNib x 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_121 : assignment (p := p) x 121 = ((parityNib x 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_122 : assignment (p := p) x 122 = ((parityNib x 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_123 : assignment (p := p) x 123 = ((x.previous 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_124 : assignment (p := p) x 124 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_125 : assignment (p := p) x 125 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_126 : assignment (p := p) x 126 = ((x.previous 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_127 : assignment (p := p) x 127 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_128 : assignment (p := p) x 128 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_129 : assignment (p := p) x 129 = ((x.previous 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_130 : assignment (p := p) x 130 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_131 : assignment (p := p) x 131 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_132 : assignment (p := p) x 132 = ((x.previous 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_133 : assignment (p := p) x 133 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_134 : assignment (p := p) x 134 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_135 : assignment (p := p) x 135 = ((x.previous 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_136 : assignment (p := p) x 136 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_137 : assignment (p := p) x 137 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_138 : assignment (p := p) x 138 = ((x.previous 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_139 : assignment (p := p) x 139 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_140 : assignment (p := p) x 140 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_141 : assignment (p := p) x 141 = ((x.previous 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_142 : assignment (p := p) x 142 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_143 : assignment (p := p) x 143 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_144 : assignment (p := p) x 144 = ((x.previous 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_145 : assignment (p := p) x 145 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_146 : assignment (p := p) x 146 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_147 : assignment (p := p) x 147 = ((x.previous 8 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_148 : assignment (p := p) x 148 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_149 : assignment (p := p) x 149 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_150 : assignment (p := p) x 150 = ((x.previous 9 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_151 : assignment (p := p) x 151 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_152 : assignment (p := p) x 152 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_153 : assignment (p := p) x 153 = ((x.previous 10 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_154 : assignment (p := p) x 154 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_155 : assignment (p := p) x 155 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_156 : assignment (p := p) x 156 = ((x.previous 11 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_157 : assignment (p := p) x 157 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_158 : assignment (p := p) x 158 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_159 : assignment (p := p) x 159 = ((x.previous 12 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_160 : assignment (p := p) x 160 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_161 : assignment (p := p) x 161 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_162 : assignment (p := p) x 162 = ((x.previous 13 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_163 : assignment (p := p) x 163 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_164 : assignment (p := p) x 164 = ((1 : Nat) : ZMod p) := rfl

end Airbender.NonVacuous.KeccakSplitSpan.Parity
