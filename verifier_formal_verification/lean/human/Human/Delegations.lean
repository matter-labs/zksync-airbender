import Human.Blake2s

/-! # Airbender's delegations (precompiles) — our own spec

A delegation call is `csrrw x0, <csr>, x0`; its arguments are pointers and a control word in registers, its data in
RAM. Each instruction is one step of the precompile (one round, one `G`, one micro-operation, …) and updates the
control register; a complete run (the decoder accepts these words only in runs of the listed lengths: `Accepted` in
`Human/Theorems.lean`) performs the whole operation. Each call is described as an `Effect` (words written, one
register); anything the precompile rejects has no next state.

Following Airbender's ISA table (zksync-airbender `spec/top-down/00 master.md`); the bit layouts of the control
words, which the table does not give, are from the sources named at each definition (marked "from source"). -/

namespace RV
open Spec

/-- The precompiles and their CSRs. -/
inductive DelegationKind | blakeRound | blakeG | bigint | keccak

def DelegationKind.csr : DelegationKind → BitVec 12
  | .blakeRound => 0x7c7 | .blakeG => 0x7c8 | .bigint => 0x7ca | .keccak => 0x7cb

def DelegationKind.ofCsr (csr : BitVec 12) : Option DelegationKind :=
  if csr = 0x7c7 then some .blakeRound else if csr = 0x7c8 then some .blakeG
  else if csr = 0x7ca then some .bigint else if csr = 0x7cb then some .keccak else none

/-- The `n` words at `addr`. -/
def readWords (mem : Word → BitVec 8) (addr : Word) (n : Nat) : Vector Word n :=
  Vector.ofFn fun i => read mem (addr + BitVec.ofNat 32 (4 * i.val)) 4

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

/-- What one delegation instruction does, given `x10`, `x11`, `x12` and memory. -/
def effect : DelegationKind → (x10 x11 x12 : Word) → (Word → BitVec 8) → Option Effect
  | .blakeRound, x10, x11, x12, mem => blakeRound x10 x11 x12 mem
  | _, _, _, _, _ => none

end Delegation

end RV
