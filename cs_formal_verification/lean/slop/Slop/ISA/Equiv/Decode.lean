import Slop.ISA.Equiv.DecUpper
import Slop.ISA.Equiv.DecBranch
import Slop.ISA.Equiv.DecLoad
import Slop.ISA.Equiv.DecStore
import Slop.ISA.Equiv.DecOpImm
import Slop.ISA.Equiv.DecOp1
import Slop.ISA.Equiv.DecOp2
import Slop.ISA.Equiv.DecMop
import Slop.ISA.Equiv.DecInput
import Slop.ISA.Equiv.DecDelegate
import Slop.ISA.Equiv.DecRev8
import Slop.ISA.Equiv.DecMopRAll
import Human.ISA.Sail.Theorems

/-! `Airbender.DecodeIsSailClaim` (`Human/ISA/Sail/Theorems.lean`): split our table `RV.decode` into its rows and use each
row's lemma (`Dec*.lean`). -/

open Lean Meta Elab Tactic
open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

theorem bits_of_toNat {w : BitVec 32} {lo n k : Nat} (h : (w.extractLsb' lo n).toNat = k) : Bits w lo n k := by
  have : (w.extractLsb' lo n).toNat = (w.toNat >>> lo) % 2 ^ n := BitVec.extractLsb'_toNat lo n w
  unfold Bits; omega

/-- The CSR rows' conditions (`RV.decodeCsr`) as known bits. -/
theorem bits_csr {w : BitVec 32} {k : Nat} {c : BitVec 12} (h : w.extractLsb' 20 12 = c) (hk : c.toNat = k) :
    Bits w 20 12 k := bits_of_toNat (by rw [h, hk])
theorem bits_src {w : BitVec 32} (h : w.extractLsb' 15 5 = 0 ∧ w.extractLsb' 7 5 ≠ 0) : Bits w 15 5 0 :=
  bits_of_toNat (by rw [h.1]; rfl)
theorem bits_rd {w : BitVec 32} (h : w.extractLsb' 15 5 ≠ 0 ∧ w.extractLsb' 7 5 = 0) : Bits w 7 5 0 :=
  bits_of_toNat (by rw [h.2]; rfl)
theorem bits_dsrc {w : BitVec 32} (h : w.extractLsb' 15 5 = 0 ∧ w.extractLsb' 7 5 = 0) : Bits w 15 5 0 :=
  bits_of_toNat (by rw [h.1]; rfl)
theorem bits_drd {w : BitVec 32} (h : w.extractLsb' 15 5 = 0 ∧ w.extractLsb' 7 5 = 0) : Bits w 7 5 0 :=
  bits_of_toNat (by rw [h.2]; rfl)

/-- Each `(w.extractLsb' lo n).toNat = k` hypothesis, also as `Bits w lo n k`. -/
elab "mk_bits" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | continue
    unless lhs.isAppOfArity ``BitVec.toNat 2 && (lhs.getArg! 1).isAppOfArity ``BitVec.extractLsb' 4 do continue
    unless (← (evalNat rhs).run).isSome do continue
    let pf ← mkAppM ``bits_of_toNat #[d.toExpr]
    let (_, g') ← (← g.assert (← mkFreshUserName `hb) (← inferType pf) pf).intro1P
    g := g'
  replaceMainGoal [g]

set_option maxHeartbeats 400000 in
theorem decode_is_sail : Airbender.DecodeIsSailClaim := by
  intro w i σ h hs
  unfold RV.decode at h
  dsimp only at h
  split at h
  all_goals (try simp only [RV.decodeCsr] at h)
  all_goals (try split_ifs at h)
  all_goals first | (cases h; done) | skip
  all_goals first | obtain rfl := Option.some.inj h | obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h | skip
  all_goals mk_bits
  all_goals first
    | exact dec_mopr w σ hs (by assumption) (by assumption) h
    | exact dec_rev8 w σ hs (by assumption) (by assumption) (by assumption)
        (bits_of_toNat (by rw [‹w.extractLsb' 20 5 = 24›]; rfl))
    | exact dec_lui w σ hs (by assumption)
    | exact dec_read w σ hs (by assumption) (by assumption) (bits_src ‹_›) (bits_csr ‹_› rfl)
    | exact dec_write w σ hs (by assumption) (by assumption) (bits_rd ‹_›) (bits_csr ‹_› rfl)
    | exact dec_delegate w σ hs (by assumption) (by assumption) (bits_dsrc ‹_›) (bits_drd ‹_›) ‹_›
    | exact dec_mop_add w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_mop_sub w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_mop_mul w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_mop_fma w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_mop_triadd w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_auipc w σ hs (by assumption)
    | exact dec_jal w σ hs (by assumption)
    | exact dec_jalr w σ hs (by assumption) (by assumption)
    | exact dec_beq w σ hs (by assumption) (by assumption)
    | exact dec_bne w σ hs (by assumption) (by assumption)
    | exact dec_blt w σ hs (by assumption) (by assumption)
    | exact dec_bge w σ hs (by assumption) (by assumption)
    | exact dec_bltu w σ hs (by assumption) (by assumption)
    | exact dec_bgeu w σ hs (by assumption) (by assumption)
    | exact dec_lb w σ hs (by assumption) (by assumption)
    | exact dec_lh w σ hs (by assumption) (by assumption)
    | exact dec_lw w σ hs (by assumption) (by assumption)
    | exact dec_lbu w σ hs (by assumption) (by assumption)
    | exact dec_lhu w σ hs (by assumption) (by assumption)
    | exact dec_sb w σ hs (by assumption) (by assumption)
    | exact dec_sh w σ hs (by assumption) (by assumption)
    | exact dec_sw w σ hs (by assumption) (by assumption)
    | exact dec_addi w σ hs (by assumption) (by assumption)
    | exact dec_slti w σ hs (by assumption) (by assumption)
    | exact dec_sltui w σ hs (by assumption) (by assumption)
    | exact dec_xori w σ hs (by assumption) (by assumption)
    | exact dec_ori w σ hs (by assumption) (by assumption)
    | exact dec_andi w σ hs (by assumption) (by assumption)
    | exact dec_slli w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_srli w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_srai w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_add w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_sub w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_mul w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_sll w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_mulhu w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_srl w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_sra w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_divu w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_remu w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_slt w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_sltu w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_xor w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_or w σ hs (by assumption) (by assumption) (by assumption)
    | exact dec_and w σ hs (by assumption) (by assumption) (by assumption)

end Slop.Equiv
