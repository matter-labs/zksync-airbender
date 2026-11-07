import Slop.ISA.Equiv.Agree
import Slop.ISA.Equiv.Run

/-! `sailOf s`: the total Sail state (`SailState`, memory a total function) that an `RV.State` stands for on the Sail
side. PC, x1..x31 and the byte memory are `s`'s; every other register is at its reset value. `Configured` holds by
construction, and `AgreeSail s (sailOf s)` holds for every `s`: no support or zero-outside premise is needed, since
the total memory is `s.loadView` itself. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

/-- Reset registers, `s`'s memory as a LOAD sees it (`loadView`; addresses are 32-bit). -/
noncomputable def sailBase (s : RV.State) : SailState :=
  { regs := Airbender.resetState.regs, mem := fun a => s.loadView (BitVec.ofNat 32 a) }

/-- Set x_n from `s` for each `n` in `ns` (in order; later writes of the same register carry the same value). -/
noncomputable def sailRegs (s : RV.State) (ns : List Nat) (σ : SailState) : SailState :=
  ns.foldl (fun σ n => xset σ (BitVec.ofNat 5 n) (s.getReg (BitVec.ofNat 5 n))) σ

/-- The Sail state of an `RV.State`: x1..x31 and the PC from `s`, memory from `s`, everything else at reset. -/
noncomputable def sailOf (s : RV.State) : SailState :=
  sailRegs s (List.range' 1 31) ((sailBase s).set .PC s.pc)

theorem set_mem' (σ : SailState) (r : Register) (v : RegisterType r) : (σ.set r v).mem = σ.mem := rfl

theorem xget_of_toNat_zero (σ : SailState) (j : BitVec 5) (h : j.toNat = 0) : xget σ j = 0 := by
  unfold xget; simp [h]

theorem sailBase_configured (s : RV.State) : Airbender.Configured (sailBase s) := fun _ _ => rfl

theorem sailRegs_configured (s : RV.State) (ns : List Nat) :
    ∀ σ, Airbender.Configured σ → Airbender.Configured (sailRegs s ns σ) := by
  induction ns with
  | nil => intro σ h; exact h
  | cons n rest ih =>
    intro σ h
    exact ih _ (sys_xset h _ _)

theorem sailRegs_mem (s : RV.State) (ns : List Nat) :
    ∀ σ, (sailRegs s ns σ).mem = σ.mem := by
  induction ns with
  | nil => intro σ; rfl
  | cons n rest ih => intro σ; exact (ih _).trans (xset_mem σ _ _)

theorem sailRegs_pc (s : RV.State) (ns : List Nat) :
    ∀ σ, (sailRegs s ns σ).regs .PC = σ.regs .PC := by
  induction ns with
  | nil => intro σ; rfl
  | cons n rest ih => intro σ; exact (ih _).trans (xset_regs σ _ _ .PC (by simp))

/-- The fold's effect on each register: `j` (≠ 0) gets `s`'s value when it is one of the written indices. -/
theorem xget_sailRegs (s : RV.State) (ns : List Nat) :
    ∀ (σ : SailState) (j : BitVec 5), (∀ n ∈ ns, n < 32) →
      xget (sailRegs s ns σ) j = if j.toNat ∈ ns ∧ j.toNat ≠ 0 then s.getReg j else xget σ j := by
  induction ns with
  | nil => intro σ j _; simp [sailRegs]
  | cons n rest ih =>
    intro σ j hn
    have hn0 : n < 32 := hn n (by simp)
    have hrest : ∀ m ∈ rest, m < 32 := fun m hm => hn m (by simp [hm])
    unfold sailRegs at ih ⊢
    simp only [List.foldl_cons]
    rw [ih _ j hrest, xget_xset]
    by_cases h0 : j.toNat = 0
    · have hj0 : j = 0 := BitVec.eq_of_toNat_eq (by simp [h0])
      rw [if_pos hj0, xget_of_toNat_zero σ j h0]
      simp [h0]
    · have hj0 : j ≠ 0 := fun h => h0 (by rw [h]; rfl)
      by_cases hjn : j.toNat = n
      · have hj : j = BitVec.ofNat 5 n := BitVec.eq_of_toNat_eq (by simp [hjn, BitVec.toNat_ofNat]; omega)
        have hmem : j.toNat ∈ n :: rest := by rw [hjn]; exact List.mem_cons_self
        rw [if_neg hj0, if_pos hj]
        simp only [hmem, h0, ne_eq, not_false_eq_true, and_true, true_and, if_true]
        by_cases hr : j.toNat ∈ rest
        · simp [hr, h0]
        · simp [hr, h0]
          rw [hj]
      · have hne : j ≠ BitVec.ofNat 5 n := by
          intro h; apply hjn; rw [h, BitVec.toNat_ofNat]; omega
        have hmem : j.toNat ∈ n :: rest ↔ j.toNat ∈ rest := by
          simp [List.mem_cons, hjn]
        rw [if_neg hj0, if_neg hne]
        by_cases hr : j.toNat ∈ rest
        · simp [hr, h0, hmem.mpr hr]
        · simp [hr, h0, hmem, hjn]

theorem sailOf_pc (s : RV.State) : (sailOf s).regs .PC = s.pc := by
  unfold sailOf
  rw [sailRegs_pc]
  exact set_regs_self _ _ _

theorem sailOf_mem (s : RV.State) (a : RV.Word) : (sailOf s).mem a.toNat = s.loadView a := by
  unfold sailOf
  rw [sailRegs_mem]
  simp [sailBase, set_mem', BitVec.ofNat_toNat]

theorem sailOf_configured (s : RV.State) : Airbender.Configured (sailOf s) := by
  unfold sailOf
  exact sailRegs_configured s _ _ (sys_set (sailBase_configured s) .PC _ rfl)

theorem sailOf_getReg (s : RV.State) (i : BitVec 5) : Airbender.getReg (sailOf s) i = s.getReg i := by
  rw [reg_eq]
  unfold sailOf
  rw [xget_sailRegs s _ _ i (by intro n hn; simp only [List.mem_range'_1] at hn; omega), xget_set_PC]
  by_cases h0 : i.toNat = 0
  · have hi : i = 0 := BitVec.eq_of_toNat_eq (by simp [h0])
    subst hi
    rw [xget_of_toNat_zero _ _ (by simp [h0])]
    simp [RV.State.getReg]
  · have hi := i.isLt
    have hm : i.toNat ∈ List.range' 1 31 := by
      simp only [List.mem_range'_1]
      omega
    simp only [hm, h0, ne_eq, not_false_eq_true, and_true, true_and, if_true]
    try rw [if_pos hm]

theorem agreeSail_sailOf (s : RV.State) : Airbender.AgreeSail s (sailOf s) :=
  ⟨sailOf_configured s, sailOf_pc s, sailOf_getReg s, sailOf_mem s⟩

end Slop.Equiv
