import Human.ISA.Blake2s
import Human.ISA.Keccak

/-! # Airbender's delegations (precompiles) — our own spec

A delegation call is `csrrw x0, <csr>, x0`; its arguments are pointers and a control word in registers, its data in
RAM. Each instruction is one step of the precompile (one round, one `G`, one micro-operation, …) and updates the
control register; a complete run (the decoder accepts these words only in runs of the listed lengths: `Accepted` at the
end) performs the whole operation. Each call is described as an `Effect` (words written, one
register); anything the precompile rejects has no next state.

Following Airbender's ISA table (zksync-airbender `spec/top-down/00 master.md`) and decoder (`av_gkr_compiler`); the
bit layouts of the control words, which the table does not give, are from the sources named at each definition (marked
"from source").

Direction of trust: a model that rejects what a circuit accepts would make "no run reaches X" claims vacuous, so where
a circuit is known to accept more than the VM (bigint, `G`, Keccak special5 controls: see each definition) the
model follows the circuit. Assumed, not audited against the circuits: the pointer conditions (in RAM, aligned,
different) and the Blake2s round mask being one-hot (the round circuit does not constrain it: "TODO" in
`cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/mod.rs`). -/

namespace RV
open Spec

/-- The precompiles and their CSRs (`ofCsr`; proofs use it only through `RV.ofCsr_csr`). Keccak-f1600 in three
circuits: CSRs `0x7cc` … `0x7ce` (`common_constants/src/delegation_types/keccak_f1600.rs`). `blakeG` (`0x7c8`) is not
in the ISA table, but Airbender's unified-machine setup still accepts it. -/
inductive DelegationKind | blakeRound | blakeG | bigint | keccak | keccakThetaRho | keccakParity | keccakChi5

def DelegationKind.csr : DelegationKind → BitVec 12
  | .blakeRound => 0x7c7 | .blakeG => 0x7c8 | .bigint => 0x7ca | .keccak => 0x7cb
  | .keccakThetaRho => 0x7cc | .keccakParity => 0x7cd | .keccakChi5 => 0x7ce

def DelegationKind.ofCsr (csr : BitVec 12) : Option DelegationKind :=
  if csr = 0x7c7 then some .blakeRound else if csr = 0x7c8 then some .blakeG
  else if csr = 0x7ca then some .bigint else if csr = 0x7cb then some .keccak
  else if csr = 0x7cc then some .keccakThetaRho else if csr = 0x7cd then some .keccakParity
  else if csr = 0x7ce then some .keccakChi5 else none

/-- The `n` words at `addr`. -/
def readWords (mem : Word → BitVec 8) (addr : Word) (n : Nat) : Vector Word n :=
  Vector.ofFn fun i => read mem (addr + BitVec.ofNat 32 (4 * i.val)) 4

/-- The 64-bit lanes at `addr` (each: low word, then high word). -/
def readLanes (mem : Word → BitVec 8) (addr : Word) (n : Nat) : Vector Lane n :=
  Vector.ofFn fun i => read mem (addr + BitVec.ofNat 32 (8 * i.val + 4)) 4 ++ read mem (addr + BitVec.ofNat 32 (8 * i.val)) 4

/-- Lanes as words: low word, then high word. -/
def laneWords {n : Nat} (ls : Vector Lane n) : Vector Word (2 * n) :=
  Vector.ofFn fun i => (ls[i.val / 2]'(by omega)).extractLsb' (32 * (i.val % 2)) 32

/-- The words of `ws` written from `addr` on, as (address, value) pairs. -/
def writesAt {n : Nat} (addr : Word) (ws : Vector Word n) : List (Word × Word) :=
  (List.finRange n).map fun i => (addr + BitVec.ofNat 32 (4 * i.val), ws[i])

namespace Delegation

/-- BLAKE2s round (CSR `0x7c7`; table: "x10 points to h[0..7] followed by v[0..15]; x11 to m[0..15]; x12 selects the
round, 7- or 10-round schedule, and mode; each instruction performs one round").
From source (`riscv_transpiler/src/vm/delegations/blake2_round_function.rs`, the per-round
`blake2_round_function_impl`; the per-call control as `replayer/delegations/blake2_round_function.rs` advances it):
`x12` bit 16 = 7 rounds, bit 17 = the input is the right node, bit 18 = compression (two-to-one) mode, bits 19 … 28
= the round, one-hot. Round 0 sets up `v`, the last round folds `v` into `h`; in compression mode the block is
`h ∥ m[0..7]` (or `m[0..7] ∥ h`) and `h` starts from the configured IV. Pointers: in RAM, 128- and 64-aligned,
different. -/
def blakeRound (x10 x11 x12 : Word) (mem : Word → BitVec 8) : Option Effect :=
  let mask := x12 >>> 19
  let r := mask.toNat.log2
  let reduced := x12.getLsbD 16
  let right := x12.getLsbD 17
  let compression := x12.getLsbD 18
  let n := if reduced then 7 else 10
  if ROM_END ≤ x10.toNat ∧ x10.toNat % 128 = 0 ∧ ROM_END ≤ x11.toNat ∧ x11.toNat + 64 ≤ RAM_END ∧
      x11.toNat % 64 = 0 ∧ x10 ≠ x11 ∧ mask = 1#32 <<< r ∧ r < n then
    let h := readWords mem x10 8          -- the state
    let e := readWords mem (x10 + 32) 16  -- the work vector (words 12, 14: counter and last-block flag)
    let m := readWords mem x11 16         -- the message block
    let v : Vector Word 16 :=
      if r ≠ 0 then e
      else if compression then
        #v[configuredIV 0, configuredIV 1, configuredIV 2, configuredIV 3, configuredIV 4, configuredIV 5,
          configuredIV 6, configuredIV 7, IV 0, IV 1, IV 2, IV 3, IV 4 ^^^ 64#32, IV 5, IV 6 ^^^ 0xFFFFFFFF#32, IV 7]
      else #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV 0, IV 1, IV 2, IV 3, e[12], IV 5, e[14], IV 7]
    let msg : Vector Word 16 :=
      if compression then
        (if right then Vector.ofFn fun i : Fin 16 => if i.val < 8 then m[i.val % 16] else h[(i.val - 8) % 8]
         else Vector.ofFn fun i : Fin 16 => if i.val < 8 then h[i.val % 8] else m[(i.val - 8) % 16])
      else m
    let v' := round msg (SIGMA ⟨r % 10, Nat.mod_lt _ (by decide)⟩) v
    let h₀ : Vector Word 8 := if compression then Vector.ofFn configuredIV else h
    let h' : Vector Word 8 := if r + 1 = n then Vector.ofFn fun i => h₀[i] ^^^ v'[i.val] ^^^ v'[i.val + 8] else h
    some { writes := writesAt x10 h' ++ writesAt (x10 + 32) v', reg := 12,
           val := (((x12 >>> 16) &&& 7#32) ||| (((mask <<< 1) &&& 0x3ff#32) <<< 3)) <<< 16 }
  else none

/-- The words of the state and message of `G` number `j` of a round (columns, then diagonals). -/
def gIndices : Fin 8 → Fin 4 → Fin 16 :=
  ![![0, 4, 8, 12], ![1, 5, 9, 13], ![2, 6, 10, 14], ![3, 7, 11, 15],
    ![0, 5, 10, 15], ![1, 6, 11, 12], ![2, 7, 8, 13], ![3, 4, 9, 14]]

/-- BLAKE2s `G` function (CSR `0x7c8`; table: "x10 → 64-aligned v[0..15], x11 → 64-aligned m[0..15]; each
instruction performs one G; runs of 56 or 80").
From source (`riscv_transpiler/src/replayer/delegations/blake2_g_function.rs`): `x12 < 256`, bits 0 … 6 = the counter
`k` (`G` number `k % 8` of round `k / 8`), bit 7 = 7 rounds (else 10, `n` = 56 / 80 calls); the counter then
advances, wrapping to 0 after the last `G`. The circuit's table (`cs/src/tables/blake_g_function_precompile_related.rs`)
also takes `k ≥ n`: `G` 0 of round 0, counter back to 0. Pointers: in RAM, 64-aligned, different. -/
def blakeG (x10 x11 x12 : Word) (mem : Word → BitVec 8) : Option Effect :=
  let k := x12.toNat % 128
  let n := if x12.getLsbD 7 then 56 else 80
  let i := if k < n then k else 0
  if ROM_END ≤ x10.toNat ∧ x10.toNat % 64 = 0 ∧ ROM_END ≤ x11.toNat ∧ x11.toNat + 64 ≤ RAM_END ∧
      x11.toNat % 64 = 0 ∧ x10 ≠ x11 ∧ x12.toNat < 256 then
    let v := readWords mem x10 16
    let m := readWords mem x11 16
    let r : Fin 10 := ⟨i / 8 % 10, Nat.mod_lt _ (by decide)⟩
    let j : Fin 8 := ⟨i % 8, Nat.mod_lt _ (by decide)⟩
    let g := gIndices j
    let v' := G v (g 0) (g 1) (g 2) (g 3) m[SIGMA r ⟨2 * j.val, by omega⟩] m[SIGMA r ⟨2 * j.val + 1, by omega⟩]
    some { writes := writesAt x10 v', reg := 12,
           val := (x12 &&& 0x80#32) ||| BitVec.ofNat 32 (if k + 1 < n then k + 1 else 0) }
  else none

/-- The 256-bit number with the 8 words `ws` (least significant first), and back. -/
def toU256 (ws : Vector Word 8) : Nat := (List.finRange 8).foldr (fun i acc => ws[i].toNat + 2 ^ 32 * acc) 0
def ofU256 (a : Nat) : Vector Word 8 := Vector.ofFn fun i => BitVec.ofNat 32 (a / 2 ^ (32 * i.val))

/-- The operation `op` (κ = the carry/borrow in) on `a`, `b`: the result `mod 2²⁵⁶` and the flag. -/
def bigintOp (op : Word) (κ : Bool) (a b : Nat) : Option (Nat × Bool) :=
  let c := if κ then 1 else 0
  let W := 2 ^ 256
  match op.toNat with
  | 0x01 => some (a + b + c, W ≤ a + b + c)          -- ADD: a + b + κ, carry out
  | 0x02 => some (W + a - (b + c), a < b + c)          -- SUB: a − b − κ, borrow out
  | 0x04 => some (W + b - (a + c), b < a + c)          -- SUB_NEGATE: b − a − κ, borrow out
  | 0x08 => some (a * b, W ≤ a * b)                    -- MUL_LOW: the low half, overflow
  | 0x10 => some (a * b / W, false)                    -- MUL_HIGH: the high half
  | 0x20 => some (a, decide (a = b))                   -- EQ: `a` unchanged, equality
  | 0x80 => some (b + c, W ≤ b + c)                    -- MEMCOPY: b + κ, carry out
  | 0x00 => some (0, false)                            -- none (the circuit; the VM rejects it): zero
  | _ => none

/-- u256 bigint (CSR `0x7ca`; table: "x10, x11 → 32-byte aligned little-endian 256-bit a, b; x12 selects ADD, SUB,
SUB_NEGATE, MUL_LOW, MUL_HIGH, EQ, MEMCOPY; the result overwrites a; x12 returns the flag").
From source (`riscv_transpiler/src/vm/delegations/bigint.rs`; the circuit
`cs/src/gkr_circuits/delegation/bigint_with_control`): the low byte of `x12` holds the bits ADD 0, SUB 1, SUB_NEGATE
2, MUL_LOW 3, MUL_HIGH 4, EQ 5, κ 6, MEMCOPY 7, at most one besides κ (`bigintOp`); bits 8 … 15 zero, bits 16 … 31
ignored by the circuit (the VM wants `x12 < 256` and exactly one operation). Pointers: in RAM, 32-aligned,
different. -/
def bigint (x10 x11 x12 : Word) (mem : Word → BitVec 8) : Option Effect :=
  if ROM_END ≤ x10.toNat ∧ x10.toNat % 32 = 0 ∧ ROM_END ≤ x11.toNat ∧ x11.toNat + 32 ≤ RAM_END ∧
      x11.toNat % 32 = 0 ∧ x10 ≠ x11 ∧ x12.toNat % 2 ^ 16 < 256 then
    (bigintOp (x12 &&& 0xbf#32) (x12.getLsbD 6) (toU256 (readWords mem x10 8)) (toU256 (readWords mem x11 8))).map
      fun (r, f) => { writes := writesAt x10 (ofU256 r), reg := 12, val := if f then 1 else 0 }
  else none

/-! ## Keccak

Airbender's Keccak circuits work on 31 lanes at `x11` (256-aligned, in RAM): the 25 lanes of the Keccak state and 6
scratch lanes. They do not move lanes for π: lane `p` of the state at the start of round `r` is in slot
`laneSlot r p` (`π^r` in the circuits' comments). One instruction does one piece of a round, picked by the control
word `x10 = op + 8 * x + 64 * r` (op, `x` < 5 the column or row, round `r`), and advances `x10` to the next piece.
ι is delayed: round `r`'s constant is added at the start of round `r + 1`, and a last call (`r = 24`) adds round
23's. -/

/-- The slot of lane `p` at the start of round `r`. -/
def laneSlot : Nat → Fin 25 → Fin 25
  | 0, p => p
  | r + 1, p => laneSlot r (piSrc p)

/-- The slot of lane `(x, y)` at the start of round `r`; scratch slot `i`. -/
def slot (r : Nat) (x y : Fin 5) : Fin 31 := (laneSlot r (lane x y)).castLE (by omega)
def scratch (i : Fin 6) : Fin 31 := ⟨25 + i.val, by omega⟩

/-- The delayed ι: round `r - 1`'s constant (none at round 0). -/
def delayedRC (r : Nat) : Lane := if h : 0 < r ∧ r ≤ 24 then RC ⟨r - 1, by omega⟩ else 0

/-- Set the five slots `f y` to `g y`. -/
def set5 (S : Vector Lane 31) (f : Fin 5 → Fin 31) (g : Fin 5 → Lane) : Vector Lane 31 :=
  (List.finRange 5).foldl (fun S y => S.set (f y) (g y)) S

/-- θ's first step, after the delayed ι (in column 0): column `x`'s parity into scratch `x`. -/
def columnParity (r : Nat) (x : Fin 5) (S : Vector Lane 31) : Vector Lane 31 :=
  let L := slot r x
  let S := if x = 0 then S.set (L 0) (S[L 0] ^^^ delayedRC r) else S
  S.set (scratch x.castSucc) (S[L 0] ^^^ S[L 1] ^^^ S[L 2] ^^^ S[L 3] ^^^ S[L 4])

/-- The six slots a Keccak special5 call reads and writes, for operation `op` on column / row `x` of round `r`:
column `x` (`L`) and scratch for ops 0, 3, 4; the scratch for ops 1, 2; row `x` after π (`a`) and scratch for ops 5,
6. From source (`keccak_special5_impl_extract_indices`); outside the pieces of a run (op 0 after round 24, the others
after round 23) the circuit's table (`cs/src/tables/keccak_precompile_related.rs`) gives slots 0 … 5. -/
def special5Slots (op : Nat) (x : Fin 5) (r : Nat) : Fin 6 → Fin 31 :=
  let L := slot r x
  let a := fun k => slot (r + 1) k x
  if op = 0 ∧ r ≤ 24 ∨ 0 < op ∧ r < 24 then
    match op with
    | 0 => ![L 0, L 1, L 2, L 3, L 4, scratch x.castSucc]
    | 1 | 2 => scratch
    | 3 => ![L 0, L 1, L 2, L 3, L 4, scratch (x - 1).castSucc]
    | 4 => ![L 0, L 1, L 2, L 3, L 4, scratch 0]
    | 5 => ![a 1, a 2, a 3, a 4, scratch 0, scratch 1]
    | _ => ![a 0, a 3, a 4, scratch 0, scratch 1, scratch 2]
  else fun i => i.castLE (by omega)

/-- What a Keccak special5 call computes from its six lanes `v` (from source: `keccak_special5_impl_compute_outputs`).
In a run: op 0 adds the delayed ι (column 0) and puts column `x`'s parity `C[x]` in scratch `x`; ops 1, 2 turn the
parities into θ's `D[1], D[2], D[3], D[4], D[0]` (scratch 0 … 4, with scratch 5); op 3 adds `D[x]` to column `x`
(θ), op 4 rotates it (ρ); ops 5, 6 compute χ on row `x`, with scratch 0, 1. -/
def special5Op (op : Nat) (x : Fin 5) (r : Nat) (v : Fin 6 → Lane) : Fin 6 → Lane :=
  let rot1 (l : Lane) := l.rotateLeft 1
  match op with
  | 0 => let v0 := v 0 ^^^ (if x = 0 then delayedRC r else 0)
         ![v0, v 1, v 2, v 3, v 4, v0 ^^^ v 1 ^^^ v 2 ^^^ v 3 ^^^ v 4]
  | 1 => ![v 0 ^^^ rot1 (v 2), v 1, v 2 ^^^ rot1 (v 4), v 3, v 4, rot1 (v 0)]
  | 2 => ![v 0, v 1 ^^^ rot1 (v 3), v 2, v 3 ^^^ v 5, v 4 ^^^ rot1 (v 1), v 5]
  | 3 => ![v 0 ^^^ v 5, v 1 ^^^ v 5, v 2 ^^^ v 5, v 3 ^^^ v 5, v 4 ^^^ v 5, v 5]
  | 4 => ![(v 0).rotateLeft (rhoOffset x 0), (v 1).rotateLeft (rhoOffset x 1), (v 2).rotateLeft (rhoOffset x 2),
           (v 3).rotateLeft (rhoOffset x 3), (v 4).rotateLeft (rhoOffset x 4), v 5]
  | 5 => ![v 0 ^^^ (~~~v 1 &&& v 2), v 1 ^^^ (~~~v 2 &&& v 3), v 2, v 3, ~~~v 0 &&& v 1, v 0]
  | _ => ![v 0 ^^^ v 3, v 1 ^^^ (~~~v 2 &&& v 0), v 2 ^^^ (~~~v 0 &&& v 4), v 3, v 4, v 5]

/-- One call of Keccak special5: read the six slots, compute, write them back. -/
def special5Step (op : Nat) (x : Fin 5) (r : Nat) (S : Vector Lane 31) : Vector Lane 31 :=
  let sl := special5Slots op x r
  let out := special5Op op x r fun i => S[sl i]
  (List.finRange 6).foldl (fun S i => S.set (sl i) (out i)) S

/-- The next piece after `(op, x, r)`: ops 0, 3, 4 per column, then 1, 2 once, then 5, 6 per row. -/
def special5Next (op x r : Nat) : Nat × Nat × Nat :=
  match op with
  | 0 | 3 | 4 => (if x = 4 then op + 1 else op, (x + 1) % 5, r)
  | 1 | 2 | 5 => (op + 1, x, r)
  | _ => (if x = 4 then 0 else 5, (x + 1) % 5, if x = 4 then r + 1 else r)

/-- The control word of `(op, x, r)`. -/
def control (op x r : Nat) : Word := BitVec.ofNat 32 (op + 8 * x + 64 * r)

/-- A Keccak call on the 31 lanes at `x11` with `x10 = control op x r`, given a `valid` piece and its `step`: all
31 lanes written back (only some change), `x10` advanced to `next`. -/
def keccakCall (valid : Nat → Nat → Nat → Prop) [∀ op x r, Decidable (valid op x r)]
    (step : Nat → Fin 5 → Nat → Vector Lane 31 → Vector Lane 31) (next : Nat → Nat → Nat → Nat × Nat × Nat)
    (x10 x11 : Word) (mem : Word → BitVec 8) : Option Effect :=
  let op := x10.toNat % 8
  let x := x10.toNat / 8 % 8
  let r := x10.toNat / 64
  if h : ROM_END ≤ x11.toNat ∧ x11.toNat % 256 = 0 ∧ x10.toNat < 2 ^ 11 ∧ x < 5 ∧ valid op x r then
    let S' := step op ⟨x, h.2.2.2.1⟩ r (readLanes mem x11 31)
    let (op', x', r') := next op x r
    some { writes := writesAt x11 (laneWords S'), reg := 10, val := control op' x' r' }
  else none

/-- Keccak special5 (CSR `0x7cb`; table: "x11 → 256-aligned 25 lanes + 6 scratch; x10 mode, iteration, round; 7
modes; runs of 649"). From source (`riscv_transpiler/src/vm/delegations/keccak_special5.rs`): `special5Step`,
`special5Next`; any op < 7, `x` < 5, `r` < 32 (the circuit: one-hot op and `x`, 5-bit round; the VM accepts only
the pieces of a run). A run of 649 from `x10 = 0` is Keccak-f[1600] on the lanes (`KeccakSpecial5Run` in
`DelegationRuns`). -/
def keccakSpecial5 (x10 x11 : Word) (mem : Word → BitVec 8) : Option Effect :=
  keccakCall (fun op _ _ => op < 7) special5Step special5Next x10 x11 mem

/-- Keccak-f1600 in three circuits (CSRs `0x7cd` column parity: op 0, `0x7cc` θ+ρ: op 3, `0x7ce` χ: op 5). From
source (`common_constants/src/delegation_types/keccak_f1600.rs`,
`riscv_transpiler/src/vm/delegations/keccak_f1600.rs`): per round 5 parity, 5 θ+ρ (column `x`), 5 χ (row `x`) calls,
then one parity call (`r = 24`, `x = 0`): 361 calls from `x10 = 0` are Keccak-f[1600] (`KeccakF1600Run` in
`DelegationRuns`). -/
def f1600Step (op : Nat) (x : Fin 5) (r : Nat) (S : Vector Lane 31) : Vector Lane 31 :=
  let L := slot r x
  let a := fun k => slot (r + 1) k x
  match op with
  | 0 => columnParity r x S
  | 3 => let d := thetaD (fun i => S[scratch i.castSucc]) x
         set5 S L fun y => (S[L y] ^^^ d).rotateLeft (rhoOffset x y)
  | _ => set5 S a fun k => S[a k] ^^^ (~~~S[a (k + 1)] &&& S[a (k + 2)])

def f1600Next (op x r : Nat) : Nat × Nat × Nat :=
  if x < 4 then (op, x + 1, r) else if op = 0 then (3, 0, r) else if op = 3 then (5, 0, r) else (0, 0, r + 1)

def keccakF1600 (op : Nat) (x10 x11 : Word) (mem : Word → BitVec 8) : Option Effect :=
  keccakCall (fun op' x r => op' = op ∧ (r < 24 ∨ r = 24 ∧ x = 0 ∧ op = 0)) f1600Step f1600Next x10 x11 mem

/-- What one delegation instruction does, given `x10`, `x11`, `x12` and memory. -/
def effect : DelegationKind → (x10 x11 x12 : Word) → (Word → BitVec 8) → Option Effect
  | .blakeRound, x10, x11, x12, mem => blakeRound x10 x11 x12 mem
  | .blakeG, x10, x11, x12, mem => blakeG x10 x11 x12 mem
  | .bigint, x10, x11, x12, mem => bigint x10 x11 x12 mem
  | .keccak, x10, x11, _, mem => keccakSpecial5 x10 x11 mem
  | .keccakParity, x10, x11, _, mem => keccakF1600 0 x10 x11 mem
  | .keccakThetaRho, x10, x11, _, mem => keccakF1600 3 x10 x11 mem
  | .keccakChi5, x10, x11, _, mem => keccakF1600 5 x10 x11 mem

end Delegation

end RV

namespace RV

/-- How many delegation calls in a row the decoder accepts (ISA table: "only exact runs of"), by instruction word:
`csrrw x0, 0x7c7, x0` 7 or 10, `0x7c8` 56 or 80, `0x7cb` 649 (`0x7ca`: any). -/
def callRun (w : Word) : Option (List Nat) :=
  if w = 0x7c701073 then some [7, 10] else if w = 0x7c801073 then some [56, 80]
  else if w = 0x7cb01073 then some [649] else none

/-- The words of a flat binary (little-endian). -/
def imageWords : List (BitVec 8) → List Word
  | b0 :: b1 :: b2 :: b3 :: rest => (b3 ++ b2 ++ b1 ++ b0) :: imageWords rest
  | _ => []

/-- The Keccak-f1600 words (`csrrw x0, 0x7cc … 0x7ce, x0`). -/
def isF1600Word (w : Word) : Bool := w == 0x7cc01073 || w == 0x7cd01073 || w == 0x7ce01073

/-- A Keccak-f1600 run (ISA table: "exact runs of 361 consecutive calls"): 24 × (5 parity `0x7cd`, 5 θ+ρ `0x7cc`,
5 χ `0x7ce`), then 1 parity. -/
def f1600Run : List Word :=
  (List.replicate 24
    (List.replicate 5 0x7cd01073 ++ List.replicate 5 0x7cc01073 ++ List.replicate 5 0x7ce01073)).flatten ++
  [0x7cd01073]

/-- The decoder accepts the binary: every maximal run of one delegation word has an accepted length, and every
maximal run of Keccak-f1600 words is one Keccak-f1600 run. -/
def Accepted (bytes : Array (BitVec 8)) : Prop :=
  (∀ run ∈ (imageWords bytes.toList).splitBy (· == ·),
    ∀ lengths ∈ run.head?.bind callRun, run.length ∈ lengths) ∧
  ∀ run ∈ (imageWords bytes.toList).splitBy (fun a b => isF1600Word a && isF1600Word b),
    run.head?.any isF1600Word → run = f1600Run

instance : DecidablePred Accepted := fun _ => by unfold Accepted; infer_instance

end RV
