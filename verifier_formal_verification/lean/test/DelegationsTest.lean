import Human.Delegations
import Human.SpecBlake
import Human.SpecMerkle
open RV Spec RV.Delegation

/-! Sanity checks of `Human/Delegations.lean` (compiled, not a proof): complete runs of each precompile, call by
call, against the standard operation (`Human/Blake2s.lean`, `Human/Keccak.lean`, `Nat` arithmetic). -/

/-- Memory holding the words `ws` from `base` on (zero elsewhere). -/
def memOf (base : Nat) (ws : Array Word) : Word → BitVec 8 := fun a =>
  if base ≤ a.toNat ∧ a.toNat < base + 4 * ws.size then
    (ws.getD ((a.toNat - base) / 4) 0 >>> (8 * (a.toNat % 4))).setWidth 8 else 0

def wordsAt (mem : Word → BitVec 8) (base n : Nat) : Array Word :=
  (Array.range n).map fun i => read mem (BitVec.ofNat 32 (base + 4 * i)) 4

/-- `n` calls of `k` from `s`, the memory re-flattened to the `size` words at `base` after each call. -/
def calls (k : DelegationKind) (base size : Nat) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => do
    let s ← (Delegation.effect k (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem).bind s.applyEffect
    calls k base size n { s with mem := memOf base (wordsAt s.mem base size) }

def start (base : Nat) (ws : Array Word) (x10 x11 x12 : Word) : State :=
  (((({ pc := 0, regFile := fun _ => 0, mem := memOf base ws } : State).setReg 10 x10).setReg 11 x11).setReg 12 x12)

def B : Nat := 0x1401000

/-- Pseudo-random words. -/
def rnd (seed n : Nat) : Array Word :=
  (Array.range n).map fun i => BitVec.ofNat 32 ((seed + 1) * 2654435761 * (i + 7) ^ 3 + i * 40503)

/-- Blake2s round function (0x7c7): 7 calls on the five-word block, laid out as `blake2s_u32` does (state, extended
state with the counter and last-block words, input at `+128`), give `blake5`. -/
def checkBlakeRound (w : List Nat) : Bool :=
  let ws : Array Word := ((List.ofFn fun i : Fin 8 => configuredIV i) ++
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20 ^^^ IV 4, 0, 0xFFFFFFFF ^^^ IV 6, 0] ++ List.replicate 8 0 ++
    w.map (BitVec.ofNat 32 ·) ++ List.replicate 11 0).toArray
  match calls .blakeRound B 48 7 (start B ws (BitVec.ofNat 32 B) (BitVec.ofNat 32 (B + 128)) ((0b1001 : Word) <<< 16)) with
  | some s => (wordsAt s.mem B 8).toList == (blake5 (Vector.ofFn fun i : Fin 5 => BitVec.ofNat 32 (w.getD i 0))).toList
  | none => false

/-- Blake2s round function (0x7c7) in compression mode (`x12 = 0b1101 << 16`: 7 rounds, two-to-one, the state at
`x10` the left half): 7 calls = `hash2`. -/
def checkCompression (seed : Nat) : Bool :=
  let ws := rnd seed 48
  let l : Vector Word 8 := Vector.ofFn fun i => ws[i.val]!
  let r : Vector Word 8 := Vector.ofFn fun i => ws[32 + i.val]!
  match calls .blakeRound B 48 7 (start B ws (BitVec.ofNat 32 B) (BitVec.ofNat 32 (B + 128)) ((0b1101 : Word) <<< 16)) with
  | some s => (wordsAt s.mem B 8).toList == (hash2 l r).toList
  | none => false

/-- G function (0x7c8): 56 calls from `x12 = 0x80` are 7 rounds of `Spec.round`; `x12` back to `0x80`. -/
def checkG (seed : Nat) : Bool :=
  let ws := rnd seed 32
  let v : Vector Word 16 := Vector.ofFn fun i => ws[i.val]!
  let m : Vector Word 16 := Vector.ofFn fun i => ws[16 + i.val]!
  let want := (List.range 7).foldl (fun v r => round m (SIGMA ⟨r % 10, by omega⟩) v) v
  match calls .blakeG B 32 56 (start B ws (BitVec.ofNat 32 B) (BitVec.ofNat 32 (B + 64)) 0x80) with
  | some s => (wordsAt s.mem B 16).toList == want.toList && s.getReg 12 == 0x80
  | none => false

/-- bigint (0x7ca) on `a`, `b`, control `x12`: the result and the flag. -/
def runBigint (x12 : Word) (a b : Nat) : Option (Nat × Nat) := do
  let s ← calls .bigint B 16 1 (start B ((ofU256 a).toArray ++ (ofU256 b).toArray) (BitVec.ofNat 32 B)
    (BitVec.ofNat 32 (B + 32)) x12)
  return (toU256 (Vector.ofFn fun i : Fin 8 => (wordsAt s.mem B 8)[i.val]!), (s.getReg 12).toNat)

def checkBigint : Bool :=
  let W := 2 ^ 256
  let a := W - 12345
  let b := 2 ^ 200 + 777
  runBigint 0x01 a b == some ((a + b) % W, 1) && runBigint 0x41 3 4 == some (8, 0) &&
  runBigint 0x02 b a == some ((W + b - a) % W, 1) && runBigint 0x42 5 4 == some (0, 0) &&
  runBigint 0x04 a b == some ((W + b - a) % W, 1) && runBigint 0x08 a b == some (a * b % W, 1) &&
  runBigint 0x10 a b == some (a * b / W, 0) && runBigint 0x20 a a == some (a, 1) && runBigint 0x20 a b == some (a, 0) &&
  runBigint 0x80 a b == some (b, 0) && runBigint 0xc0 (W - 1) (W - 1) == some (0, 1) &&
  runBigint 0x03 a b == none && runBigint 0x100 a b == none &&
  -- what the circuit also accepts: no operation (a := 0, flag 0), x12's high half ignored
  runBigint 0x00 a b == some (0, 0) && runBigint 0x40 a b == some (0, 0) && runBigint 0x10001 3 4 == some (7, 0)

/-- The lanes as a `Vector Lane 25`. -/
def lanes (ws : Array Word) : Vector Lane 25 := Vector.ofFn fun i => ws[2 * i.val + 1]! ++ ws[2 * i.val]!

/-- Keccak (0x7cb: 649 calls; 0x7cc … 0x7ce: 361 calls in the order of the source's run): from `x10 = 0` the
lanes are Keccak-f[1600] of the lanes; `x10` ends at 1544. -/
def checkKeccak (seed : Nat) : Bool :=
  let ws := rnd seed 62
  let want := keccakF (lanes ws)
  let s₀ := start B ws 0 (BitVec.ofNat 32 B) 0
  let special5 := calls .keccak B 62 649 s₀
  let f1600 : Option State := (List.range 24).foldl (fun s _ => s.bind fun s => do
      let s ← calls .keccakParity B 62 5 s
      let s ← calls .keccakThetaRho B 62 5 s
      calls .keccakChi5 B 62 5 s) (some s₀) |>.bind (calls .keccakParity B 62 1)
  [special5, f1600].all fun
    | some s => (lanes (wordsAt s.mem B 50)).toList == want.toList && s.getReg 10 == 1544
    | none => false

/-- The slot map against the source's table (`KECCAK_F1600_PERMUTATIONS`, rows 1 and 24) and the standard
Keccak-f[1600] test vector on the zero state. -/
def checkKeccakTables : Bool :=
  (List.finRange 25).map (fun p => (laneSlot 1 p).val) ==
    [0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21] &&
  (List.finRange 25).all (fun p => laneSlot 24 p == p) &&
  (keccakF (Vector.replicate 25 0))[0] == 0xF1258F7940E1DDE7 && (keccakF (Vector.replicate 25 0))[1] == 0x84D5CCF933C0478A

/-- RFC 7693 Appendix B: BLAKE2s-256("abc") = 508c5e8c 327c14e2 e1a72ba3 4eeb452f 37458b20 9ed63a29 4d999b4c 86675982
(digest bytes; words little-endian), as one compression with 10 rounds, counter 3, last block. -/
def checkBlakeRFC : Bool :=
  (compressRounds 10 (Vector.ofFn configuredIV) #v[0x00636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3#32 true).toList
    == [0x8C5E8C50, 0xE2147C32, 0xA32BA7E1, 0x2F45EB4E, 0x208B4537, 0x293AD69E, 0x4C9B994D, 0x82596786]

def delegationChecks : IO Bool := do
  let mut ok := true
  for (name, good) in [("blake2s round (0x7c7) x 7 = blake5", checkBlakeRound [5, 1, 2, 3, 4] &&
        checkBlakeRound [123456789, 2013265920, 7, 0, 1234567]),
      ("blake2s round (0x7c7) compression mode x 7 = hash2", checkCompression 0 && checkCompression 1),
      ("blake2s G (0x7c8) x 56 = 7 rounds", checkG 0 && checkG 1),
      ("bigint (0x7ca) ops and flags", checkBigint),
      ("keccak tables, keccakF test vector", checkKeccakTables),
      ("blake2s RFC 7693 test vector (abc)", checkBlakeRFC),
      ("keccak special5 (0x7cb) x 649, f1600 (0x7cc-0x7ce) x 361 = keccakF", checkKeccak 0 && checkKeccak 1)] do
    IO.println s!"delegation: {name}: {if good then "OK" else "MISMATCH"}"
    ok := ok && good
  return ok
