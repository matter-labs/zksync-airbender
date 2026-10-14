import Slop.Equiv.ExecAlu
import Slop.Equiv.Walk

/-! Sail's early-return monad `SailME`, peeled off once (`me_run_*`), and `jump_to` on an aligned target. -/

open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

theorem me_run_pure {α : Type} (v : α) : PreSail.PreSailME.run (pure v : SailME α α) = pure v := rfl

theorem me_run_lift_bind {α β : Type} (m : SailM α) (f : α → SailME β β) :
    PreSail.PreSailME.run (liftM m >>= f) = m >>= fun a => PreSail.PreSailME.run (f a) := by
  induction m with
  | pure a => rfl
  | impure eff cont ih =>
    show FreeM.impure _ _ = FreeM.impure _ _
    congr 1; funext v; exact ih v

theorem me_run_ite {α : Type} (c : Prop) [Decidable c] (A B : SailME α α) :
    PreSail.PreSailME.run (if c then A else B) = if c then PreSail.PreSailME.run A else PreSail.PreSailME.run B := by
  split <;> rfl

theorem bit0_of_aligned (t : BitVec 32) (ht : t.toNat % 4 = 0) : (Sail.BitVec.access t 0 == 0#1) = true := by
  have : t[0] = false := by
    rw [← BitVec.getLsbD_eq_getElem]; simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]; simp; omega
  simp [Sail.BitVec.access, this]
theorem bit1_of_aligned (t : BitVec 32) (ht : t.toNat % 4 = 0) : bit_to_bool (Sail.BitVec.access t 1) = false := by
  have : t[1] = false := by
    rw [← BitVec.getLsbD_eq_getElem]; simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]; simp; omega
  simp [Sail.BitVec.access, bit_to_bool, this]; rfl

theorem jump_to_run (σ : SailState) (hs : Airbender.Configured σ) (t : BitVec 32) (ht : t.toNat % 4 = 0) :
    runSail (jump_to t) σ = .ok RETIRE_SUCCESS (σ.set .nextPC t) := by
  unfold jump_to SailME.run
  simp only [ext_control_check_pc, me_run_lift_bind, me_run_ite, bit0_of_aligned t ht, bit1_of_aligned t ht]
  have hz : runSail (currentlyEnabled .Ext_Zca) σ = .ok false σ := en_run hs _ _ (by decide +kernel)
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Slop.runF_bind, hz, set_next_pc, Slop.runF_writeReg,
    Slop.runF_pure, PreSail.assert, me_run_pure]
  rw [show runSail (FreeM.pure () : SailM Unit) σ = .ok () σ from rfl]
  simp only [hz]

end Slop.Equiv
