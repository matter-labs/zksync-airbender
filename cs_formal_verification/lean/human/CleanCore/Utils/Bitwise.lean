module
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Linarith
-- Clean's Mathlib/Lean imports for this file, re-exported so importers see what they saw through Clean
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Std.Tactic.BVDecide

/-! # 64- and 32-bit word operations on naturals (Clean `Clean.Utils.Bitwise`, pinned b41c196): the operations the
Keccak-f[1600] and BLAKE3/Blake2s specs use, and the lemmas our proofs cite; transcribed with proofs. -/

@[expose] public section

namespace Airbender

def not64 (a : ℕ) : ℕ := a ^^^ 0xffffffffffffffff

def add32 (a b : ℕ) : ℕ := (a + b) % 2^32

def rotRight64 (x : ℕ) (offset : ℕ) : ℕ :=
  let offset := offset % 64
  let low := x % (2^offset)
  let high := x / (2^offset)
  low * (2^(64-offset)) + high

def rotRight32 (x : ℕ) (offset : ℕ) : ℕ :=
  let offset := offset % 32
  let low := x % (2^offset)
  let high := x / (2^offset)
  low * (2^(32-offset)) + high

def rotLeft64 (value : ℕ) (left : Fin 64) : ℕ:=
  let right := (64 - left) % 64
  rotRight64 value right

end Airbender
