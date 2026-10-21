import Slop.Equiv.DecUpper
import Slop.Equiv.DecBranch
import Slop.Equiv.DecLoad
import Slop.Equiv.DecStore
import Slop.Equiv.DecOpImm
import Slop.Equiv.DecOp1
import Slop.Equiv.DecOp2
import Slop.Equiv.DecMop
import Slop.Equiv.DecInput
import Slop.Equiv.DecDelegate
import HumanSail.Theorems

/-! `Airbender.DecodeIsSail` (`HumanSail/Theorems.lean`): split our table `RV.decode` into its rows and use each
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

/-- JALR outside `ExtraEncoding` has funct3 = 0. -/
theorem jalr_f3 (w : BitVec 32) (hopc : (w.extractLsb' 0 7).toNat = 103) (hl : ¬ Airbender.ExtraEncoding w) :
    (w.extractLsb' 12 3).toNat = 0 := by
  have hop : BitVec.extractLsb' 0 7 w = 0b1100111#7 := by apply BitVec.eq_of_toNat_eq; simpa using hopc
  by_contra hne
  apply hl
  left
  exact ⟨hop, fun h => hne (by rw [h]; rfl)⟩

/-- SLT, SLTU, XOR, OR, AND outside `ExtraEncoding` (and not M, funct7 ≠ 1) have funct7 = 0. -/
theorem op_f7 (w : BitVec 32) (k : Nat) (hopc : (w.extractLsb' 0 7).toNat = 51)
    (hf3 : (w.extractLsb' 12 3).toNat = k) (hk : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 7)
    (h1 : (w.extractLsb' 25 7).toNat = 1 → False) (hl : ¬ Airbender.ExtraEncoding w) :
    (w.extractLsb' 25 7).toNat = 0 := by
  unfold Airbender.ExtraEncoding at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, not_and] at hl
  have hop : BitVec.extractLsb' 0 7 w = 0b0110011#7 := by apply BitVec.eq_of_toNat_eq; simpa using hopc
  have e : BitVec.extractLsb' 12 3 w = BitVec.ofNat 3 k := by
    apply BitVec.eq_of_toNat_eq; rw [hf3, BitVec.toNat_ofNat]; omega
  have hf : BitVec.extractLsb' 12 3 w = 2#3 ∨ BitVec.extractLsb' 12 3 w = 3#3 ∨ BitVec.extractLsb' 12 3 w = 4#3 ∨
      BitVec.extractLsb' 12 3 w = 6#3 ∨ BitVec.extractLsb' 12 3 w = 7#3 := by
    rw [e]; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
  have := hl.2 hop hf
  by_contra hne
  exact this (by intro h; apply hne; simpa using congrArg BitVec.toNat h) (by intro h; apply h1; simpa using congrArg BitVec.toNat h)

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
theorem decode_is_sail : Airbender.DecodeIsSail := by
  intro w i σ h hl hs
  unfold RV.decode at h
  dsimp only at h
  split at h
  all_goals (try simp only [RV.decodeCsr] at h)
  all_goals (try split_ifs at h)
  all_goals first | (cases h; done) | skip
  all_goals first | obtain rfl := Option.some.inj h | obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
  all_goals (try have := jalr_f3 w ‹_› hl)
  all_goals first
    | have := op_f7 w 2 ‹_› ‹_› (by decide) ‹_› hl
    | have := op_f7 w 3 ‹_› ‹_› (by decide) ‹_› hl
    | have := op_f7 w 4 ‹_› ‹_› (by decide) ‹_› hl
    | have := op_f7 w 6 ‹_› ‹_› (by decide) ‹_› hl
    | have := op_f7 w 7 ‹_› ‹_› (by decide) ‹_› hl
    | skip
  all_goals mk_bits
  all_goals first
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
