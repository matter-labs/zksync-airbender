import Slop.Sym.Meta
import Human.SpecBlake
import Mathlib.Data.BitVec

/-! # Blake2s as the compiler emits it, for executor proofs

The value DAG of the compression is cut at the four outputs of every `G` (found by evaluation, `gen/blake.py`).
Each `G` is one lemma (`g_cluster`): rotations come out as `srl`/`sll`/`or` (`rotr*`), additions reassociated (AC
normalisation). The 56 `G`s are then chained on the 16-word working vector (`G_step`). -/

namespace RV
open Sym

/-- The four new words of `G` (`Spec.G` is this, written into the vector). -/
def gOut (va vb vc vd x y : Word) : Word × Word × Word × Word :=
  let a₁ := va + vb + x
  let d₁ := (vd ^^^ a₁).rotateRight 16
  let c₁ := vc + d₁
  let b₁ := (vb ^^^ c₁).rotateRight 12
  let a₂ := a₁ + b₁ + y
  let d₂ := (d₁ ^^^ a₂).rotateRight 8
  let c₂ := c₁ + d₂
  let b₂ := (b₁ ^^^ c₂).rotateRight 7
  (a₂, b₂, c₂, d₂)

theorem G_eq (v : Vector Word 16) (a b c d : Fin 16) (x y : Word) :
    Spec.G v a b c d x y = let q := gOut v[a] v[b] v[c] v[d] x y
      (((v.set a q.1).set b q.2.1).set c q.2.2.1).set d q.2.2.2 := rfl

/-- One `G` on the working vector, from its four new words. -/
theorem G_step {v v' : Vector Word 16} {a b c d : Fin 16} {x y A B C D : Word}
    (hq : gOut v[a] v[b] v[c] v[d] x y = (A, B, C, D)) (hv : (((v.set a A).set b B).set c C).set d D = v') :
    Spec.G v a b c d x y = v' := by
  rw [G_eq]; simp only [hq]; exact hv

/-! Rotations as compiled for RV32IM (no `ror`): `(x >> k) | (x << (32 - k))`, either operand order. -/
theorem rotr16 (x : Word) : alu .or (alu .srl x 16#32) (alu .sll x 16#32) = x.rotateRight 16 := by
  rfl
theorem rotl16 (x : Word) : alu .or (alu .sll x 16#32) (alu .srl x 16#32) = x.rotateRight 16 := by
  rw [show alu .or _ _ = alu .or _ _ from BitVec.or_comm _ _]; rfl
theorem rotr12 (x : Word) : alu .or (alu .srl x 12#32) (alu .sll x 20#32) = x.rotateRight 12 := by
  rfl
theorem rotl12 (x : Word) : alu .or (alu .sll x 20#32) (alu .srl x 12#32) = x.rotateRight 12 := by
  rw [show alu .or _ _ = alu .or _ _ from BitVec.or_comm _ _]; rfl
theorem rotr8 (x : Word) : alu .or (alu .srl x 8#32) (alu .sll x 24#32) = x.rotateRight 8 := by
  rfl
theorem rotl8 (x : Word) : alu .or (alu .sll x 24#32) (alu .srl x 8#32) = x.rotateRight 8 := by
  rw [show alu .or _ _ = alu .or _ _ from BitVec.or_comm _ _]; rfl
theorem rotr7 (x : Word) : alu .or (alu .srl x 7#32) (alu .sll x 25#32) = x.rotateRight 7 := by
  rfl
theorem rotl7 (x : Word) : alu .or (alu .sll x 25#32) (alu .srl x 7#32) = x.rotateRight 7 := by
  rw [show alu .or _ _ = alu .or _ _ from BitVec.or_comm _ _]; rfl

theorem xor_left_comm' (a b c : Word) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

/-- A `G` (or any add/xor/rotate piece) after `sym_unfold`: rotations, then equality up to AC of `+` and `^^^`. -/
macro "g_cluster" : tactic => `(tactic| (
  sym_generalize
  simp only [RV.rotr16, RV.rotl16, RV.rotr12, RV.rotl12, RV.rotr8, RV.rotl8, RV.rotr7, RV.rotl7]
  simp only [RV.alu, RV.gOut, Prod.mk.injEq]
  simp only [add_assoc, add_comm, add_left_comm, BitVec.xor_assoc, BitVec.xor_comm, RV.xor_left_comm', and_self]))

/-- One operation of `G` after `sym_unfold`: a 3-term sum, or a rotation of an xor (operands in any order). -/
macro "op_cluster" : tactic => `(tactic| (
  sym_generalize
  try simp only [RV.rotr16, RV.rotl16, RV.rotr12, RV.rotl12, RV.rotr8, RV.rotl8, RV.rotr7, RV.rotl7]
  try simp only [RV.alu]
  all_goals first | ac_rfl | simp only [add_assoc, add_comm, add_left_comm, BitVec.xor_comm]))

end RV
