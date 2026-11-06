import Slop.Sail.MMIO

namespace Tests.SailMMIO
open Airbender.Reference Airbender.Reference.RiscV.Sail
set_option warningAsError true

private def configured : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .mhartid 0
      |>.insert .htif_tohost_base none }

theorem ram_read :
    Sail.run (SailRV32.Functions.within_mmio_readable (.Physaddr 4194304) 4) configured =
      .ok false configured := by
  apply mmio_read_excluded (hart := 0) (address := 4194304)
  all_goals first
    | (solve | simp [configured, Std.ExtDHashMap.get?_insert]; try rfl)
    | (unfold OrdinaryWordAddress; decide)

theorem ram_write :
    Sail.run (SailRV32.Functions.within_mmio_writable (.Physaddr 4194304) 4) configured =
      .ok false configured := by
  apply mmio_write_excluded (hart := 0) (address := 4194304)
  all_goals first
    | (solve | simp [configured, Std.ExtDHashMap.get?_insert]; try rfl)
    | (unfold OrdinaryWordAddress; decide)

theorem windows_excluded : ¬ OrdinaryWordAddress 33554432 ∧ ¬ OrdinaryWordAddress 201326592 :=
  by unfold OrdinaryWordAddress; decide

-- The Airbender configuration does not enable the signature device (`plat_have_sig = false`): the
-- window at 0xC000000 is ordinary memory here, not MMIO (the stock configuration had it).
theorem signature_is_not_mmio :
    Sail.run (SailRV32.Functions.within_mmio_readable (.Physaddr 201326592) 4) configured =
      .ok false configured := by
  have hart : configured.regs.get? .mhartid = some (0 : BitVec 32) := by
    simp [configured, Std.ExtDHashMap.get?_insert]
  have host : configured.regs.get? .htif_tohost_base = some none := by simp [configured]
  have clint : Sail.run (SailRV32.Functions.within_clint (.Physaddr 201326592) 4) configured =
      .ok false configured := clint_excluded (address := 201326592) hart (Or.inr (by decide))
  have signature : SailRV32.Functions.within_sig (.Physaddr 201326592) 4 = pure false := rfl
  simp only [SailRV32.Functions.within_mmio_readable, SailRV32.Functions.get_config_rvfi,
    Bool.false_eq_true, ite_false]
  rw [Sail.run_bind_of_ok _ _ _ _ _ clint]
  simp only [signature, Sail.freeM_pure_bind, SailRV32.Functions.within_htif_readable]
  rw [Sail.run_bind_of_ok _ _ _ _ _ (htif_disabled host _ 4)]
  rfl

end Tests.SailMMIO
