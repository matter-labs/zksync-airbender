module
public import Human.ISA.DelegationRuns

@[expose] public section
namespace RV.ValidUse
open Spec

/-- A delegation buffer lies in architectural RAM and has its reference alignment and extent. -/
def RAMBuffer (pointer : Word) (bytes alignment : Nat) : Prop :=
  ROM_END ≤ pointer.toNat ∧ Buffer pointer bytes alignment

/-- Bigint controls select exactly one supported operation and an optional carry bit. -/
def BigintControl (control : Word) : Prop :=
  control.toNat < 256 ∧ (control &&& 0xbf#32).toNat ∈ [1, 2, 4, 8, 16, 32, 128]

/-- Valid bigint arguments use separate aligned RAM buffers and a supported control. -/
def Bigint (state : State) : Prop :=
  RAMBuffer (state.getReg 10) 32 32 ∧ RAMBuffer (state.getReg 11) 32 32 ∧
    Apart (state.getReg 10) 32 (state.getReg 11) 32 ∧ BigintControl (state.getReg 12)

/-- The G reference ABI starts at its first call with separate aligned RAM buffers.
    The RAM bounds state the public ABI; the algebraic result also holds in shadow RAM. -/
def G (reduced : Bool) (state : State) (left right : Word) : Prop :=
  ROM_END ≤ left.toNat ∧ ROM_END ≤ right.toNat ∧ Apart left 64 right 64 ∧
    BlakeGAssumptions (if reduced then 0x80#32 else 0#32) state left right

/-- The round reference ABI uses the first one-hot round and the public counter and final-block flag.
    The RAM bounds state the public ABI; the algebraic result also holds in shadow RAM. -/
def Round (reduced : Bool) (state : State) (left right counter : Word) (last : Bool) : Prop :=
  ROM_END ≤ left.toNat ∧ ROM_END ≤ right.toNat ∧
    BlakeCompressAssumptions (if reduced then 0x90000#32 else 0x80000#32) state left right counter last

/-- The hash ABI selects compression mode, its input side and its first one-hot round.
    The RAM bounds state the public ABI; the algebraic result also holds in shadow RAM. -/
def Hash (reduced right : Bool) (state : State) (left sibling : Word) : Prop :=
  ROM_END ≤ left.toNat ∧ ROM_END ≤ sibling.toNat ∧
    BlakeHashAssumptions (if reduced then (if right then 0xf0000#32 else 0xd0000#32)
      else (if right then 0xe0000#32 else 0xc0000#32)) state left sibling

/-- The complete Keccak reference ABI starts with control zero and a 256-byte-aligned RAM state.
    The RAM bound states the public ABI; the algebraic result also holds in shadow RAM. -/
def Keccak (state : State) (pointer : Word) : Prop :=
  ROM_END ≤ pointer.toNat ∧ KeccakAssumptions state pointer

/-- Decode eight little-endian words by bit-vector concatenation. -/
def bigintValue (words : Vector Word 8) : BitVec 256 :=
  words[7] ++ words[6] ++ words[5] ++ words[4] ++ words[3] ++ words[2] ++ words[1] ++ words[0]

/-- Extract the eight little-endian words of a 256-bit value. -/
def bigintWords (value : BitVec 256) : Vector Word 8 :=
  Vector.ofFn fun index => value.extractLsb' (32 * index.val) 32

/-- The u256 operations use bit-vector arithmetic and unsigned carry, borrow and equality flags. -/
def bigintOperation (code : Nat) (carry : Bool) (left right : BitVec 256) : Option (BitVec 256 × Bool) :=
  let incoming : BitVec 256 := if carry then 1 else 0
  match code with
  | 1 => some (left + right + incoming, 2 ^ 256 ≤ left.toNat + right.toNat + incoming.toNat)
  | 2 => some (left - right - incoming, left.toNat < right.toNat + incoming.toNat)
  | 4 => some (right - left - incoming, right.toNat < left.toNat + incoming.toNat)
  | 8 => some (left * right, 2 ^ 256 ≤ left.toNat * right.toNat)
  | 16 => some (((left.zeroExtend 512) * (right.zeroExtend 512)).extractLsb' 256 256, false)
  | 32 => some (left, decide (left.toNat = right.toNat))
  | 128 => some (right + incoming, 2 ^ 256 ≤ right.toNat + incoming.toNat)
  | _ => none

/-- The independent bigint reference uses concatenation, u256 arithmetic and word extraction. -/
def bigintReference (state : State) : Option Effect :=
  (bigintOperation ((state.getReg 12) &&& 0xbf#32).toNat ((state.getReg 12).getLsbD 6)
    (bigintValue (readWords state.mem (state.getReg 10) 8))
    (bigintValue (readWords state.mem (state.getReg 11) 8))).map fun result =>
      { writes := writesAt (state.getReg 10) (bigintWords result.1), reg := 12, val := if result.2 then 1 else 0 }

/-- The independent seven- or ten-round BLAKE2s state update. -/
def gReference (reduced : Bool) (state message : Vector Word 16) : Vector Word 16 :=
  if reduced then (List.finRange 7).foldl (fun v r => round message (SIGMA (r.castLE (by decide))) v) state
  else (List.finRange 10).foldl (fun v r => round message (SIGMA r) v) state

end RV.ValidUse
