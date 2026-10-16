import Human.Blake2s

/-! # Airbender's delegations (precompiles) — our own spec

A delegation call is a run of identical `csrrw x0, <csr>, x0` words (any Zicsr form, source and `rd` both 0) that
Airbender's transpiler turns into one call of a custom circuit; the arguments are pointers and flags in `x10 …`.
The call takes as many instruction slots as the run is long; a run that does not start at the PC, or whose length
does not match the call, has no next state (`RV.isRun`).

Modelled: the Blake2s round function with extended control, CSR `0x7c7` (the verifier's `blake2s_u32` with feature
`blake2_with_compression`), transcribed from zksync-airbender
`riscv_transpiler/src/vm/delegations/blake2_round_function.rs`.
Not modelled (no next state): CSR `0x7c8` (Blake2s G function), `0x7ca` (u256 bigint), `0x7cb … 0x7ce` (Keccak). -/

namespace RV
open Spec

/-- The `n` words at `addr`. -/
def readWords (mem : Word → BitVec 8) (addr : Word) (n : Nat) : Vector Word n :=
  Vector.ofFn fun i => read mem (addr + BitVec.ofNat 32 (4 * i.val)) 4

/-- The first `k` rounds (message schedule rows `0 … k-1`) on the working vector `v`, message `m`. -/
def rounds (m : Vector Word 16) : Nat → Vector Word 16 → Vector Word 16
  | 0,     v => v
  | k + 1, v => round m (SIGMA ⟨k % 10, Nat.mod_lt _ (by decide)⟩) (rounds m k v)

namespace Delegation

/-- The Blake2s round-function call (CSR `0x7c7`). `x10`: the 128-aligned state (8 words) followed by the extended
state (16 words); `x11`: the 64-aligned 16-word input block; `x12`: the control register — bit 16: 7 rounds (else
10), bit 17: the input is the right node, bit 18: compression mode (a Merkle node: state and input half hashed
as one block); bits 19 and up: the round mask, `1` at the start of a call.
Gives the number of rounds (= instruction slots of the call), the new `x12`, and the 24 words written back at
`x10` (the new state, then the final working vector); `none`: Airbender rejects the call. -/
def blake2s (x10 x11 x12 : Word) (mem : Word → BitVec 8) : Option (Nat × Word × Vector Word 24) :=
  if ROM_END ≤ x10.toNat ∧ x10.toNat + 96 ≤ RAM_END ∧ x10.toNat % 128 = 0 ∧
     ROM_END ≤ x11.toNat ∧ x11.toNat + 64 ≤ RAM_END ∧ x11.toNat % 64 = 0 ∧ x10 ≠ x11 ∧ x12 >>> 19 = 1 then
    let reduced := x12.getLsbD 16
    let right := x12.getLsbD 17
    let compression := x12.getLsbD 18
    let n := if reduced then 7 else 10
    let h := readWords mem x10 8           -- the state
    let e := readWords mem (x10 + 32) 16   -- the extended state (words 12, 14: counter and last-block flag)
    let m := readWords mem x11 16          -- the input
    let v₀ : Vector Word 16 :=
      if compression then
        #v[configuredIV 0, configuredIV 1, configuredIV 2, configuredIV 3, configuredIV 4, configuredIV 5,
          configuredIV 6, configuredIV 7, IV 0, IV 1, IV 2, IV 3, IV 4 ^^^ 64#32, IV 5, IV 6 ^^^ 0xFFFFFFFF#32, IV 7]
      else #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV 0, IV 1, IV 2, IV 3, e[12], IV 5, e[14], IV 7]
    let msg : Vector Word 16 :=
      if compression then
        (if right then Vector.ofFn fun i : Fin 16 => if i.val < 8 then m[i.val % 16] else h[(i.val - 8) % 8]
         else Vector.ofFn fun i : Fin 16 => if i.val < 8 then h[i.val % 8] else m[(i.val - 8) % 16])
      else m
    let v := rounds msg n v₀
    let h₀ : Vector Word 8 := if compression then Vector.ofFn configuredIV else h
    let h' : Vector Word 8 := Vector.ofFn fun i => h₀[i] ^^^ v[i.val] ^^^ v[i.val + 8]
    let x12' := (((x12 >>> 16) &&& 7#32) ||| (if reduced then 0x400#32 else 0#32)) <<< 16
    some (n, x12', Vector.ofFn fun i : Fin 24 => if i.val < 8 then h'[i.val % 8] else v[(i.val - 8) % 16])
  else none

end Delegation

/-- Airbender (transpiler): the word `w` at `pc` begins a run of exactly `n` copies of itself. -/
abbrev isRun (mem : Word → BitVec 8) (pc w : Word) (n : Nat) : Prop :=
  pc.toNat + 4 * n + 4 ≤ ROM_END ∧ (∀ k < n, read mem (pc + BitVec.ofNat 32 (4 * k)) 4 = w) ∧
  read mem (pc + BitVec.ofNat 32 (4 * n)) 4 ≠ w ∧ (pc = 0 ∨ read mem (pc - 4) 4 ≠ w)

end RV
