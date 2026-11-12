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

/-- The G reference ABI starts at its first call with separate aligned RAM buffers. -/
def G (reduced : Bool) (state : State) (left right : Word) : Prop :=
  ROM_END ≤ left.toNat ∧ ROM_END ≤ right.toNat ∧ Apart left 64 right 64 ∧
    BlakeGAssumptions (if reduced then 0x80#32 else 0#32) state left right

/-- The round reference ABI uses the first one-hot round and the public counter and final-block flag. -/
def Round (reduced : Bool) (state : State) (left right counter : Word) (last : Bool) : Prop :=
  ROM_END ≤ left.toNat ∧ ROM_END ≤ right.toNat ∧
    BlakeCompressAssumptions (if reduced then 0x90000#32 else 0x80000#32) state left right counter last

/-- The hash ABI selects compression mode, its input side and its first one-hot round. -/
def Hash (reduced right : Bool) (state : State) (left sibling : Word) : Prop :=
  ROM_END ≤ left.toNat ∧ ROM_END ≤ sibling.toNat ∧
    BlakeHashAssumptions (if reduced then (if right then 0xf0000#32 else 0xd0000#32)
      else (if right then 0xe0000#32 else 0xc0000#32)) state left sibling

/-- The complete Keccak reference ABI starts with control zero and a 256-byte-aligned RAM state. -/
def Keccak (state : State) (pointer : Word) : Prop :=
  ROM_END ≤ pointer.toNat ∧ KeccakAssumptions state pointer

/-- The independent bigint operation, encoded as the delegation's writes and return flag. -/
def bigintReference (state : State) : Option Effect :=
  (Delegation.bigintOp ((state.getReg 12) &&& 0xbf#32) ((state.getReg 12).getLsbD 6)
    (Delegation.toU256 (readWords state.mem (state.getReg 10) 8))
    (Delegation.toU256 (readWords state.mem (state.getReg 11) 8))).map fun result =>
      { writes := writesAt (state.getReg 10) (Delegation.ofU256 result.1), reg := 12, val := if result.2 then 1 else 0 }

/-- The independent seven- or ten-round BLAKE2s state update. -/
def gReference (reduced : Bool) (state message : Vector Word 16) : Vector Word 16 :=
  if reduced then (List.finRange 7).foldl (fun v r => round message (SIGMA (r.castLE (by decide))) v) state
  else (List.finRange 10).foldl (fun v r => round message (SIGMA r) v) state

end RV.ValidUse
