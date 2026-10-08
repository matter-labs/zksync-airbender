import Airbender.Proofs.Sail.PMP

namespace Tests.SailPMP
open Airbender.Reference Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true

private def configured (entry : BitVec 8) : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .pmpcfg_n (Vector.replicate 64 entry)
      |>.insert .pmpaddr_n (Vector.replicate 64 0x02000000) }

theorem off_entries :
    Sail.run (SailRV32.Functions.pmpCheck (.Physaddr 0xfffffffc) 4 (.Load .Data) .Machine)
      (configured 0) = .ok none (configured 0) := by
  apply machine_pmp_off (addresses := Vector.replicate 64 0x02000000)
  all_goals simp [configured, Std.ExtDHashMap.get?_insert]

-- Machine mode must still respect a locked matching entry with R/W/X clear.
set_option maxRecDepth 4096 in
theorem locked_entry_rejects :
    Sail.run (SailRV32.Functions.pmpCheck (.Physaddr 4194304) 4 (.Load .Data) .Machine)
      (configured 0x88) = .ok (some (.E_Load_Access_Fault ())) (configured 0x88) := by
  have config : (configured 0x88).regs.get? .pmpcfg_n =
      some (Vector.replicate 64 0x88) := by simp [configured, Std.ExtDHashMap.get?_insert]
  have addresses : (configured 0x88).regs.get? .pmpaddr_n =
      some (Vector.replicate 64 0x02000000) := by simp [configured]
  have read : Sail.run (SailRV32.Functions.pmpReadAddrReg 0) (configured 0x88) =
      .ok 0x02000000 (configured 0x88) := by
    simpa using pmp_read_address config addresses (0 : Fin 64)
  have entry (index : Int) (bound : index.toNat < 64) :
      (Vector.replicate 64 (0x88 : BitVec 8))[index]'bound = 0x88 := by
    change (Vector.replicate 64 (0x88 : BitVec 8))[index.toNat] = 0x88
    simp
  have matched : SailRV32.Functions.pmpMatchAddr (.Physaddr 4194304)
      (SailRV32.Functions.to_bits (l := 32) (4 : Nat)) 0x88 0x02000000
      (SailRV32.Functions.zeros (n := 32)) =
      pure .PMP_Match := rfl
  simp only [SailRV32.Functions.pmpCheck, SailRV32.Functions.sys_pmp_count,
    show ((16 : Int) == 0) = false from rfl, Bool.false_eq_true, ite_false,
    forIn_eq_forIn', SailRV32.SailME.run, Sail.freeM_pure_bind]
  dsimp only [ForIn'.forIn', IntRange.forIn']
  rw [IntRange.forIn'.loop]
  norm_num [Membership.mem, IntRange.instMemIntRange]
  repeat rw [Sail.freeM_bind_assoc]
  rw [Sail.early_return_lift_bind, Sail.run_bind_of_ok _ _ _ _ _ (read_register config)]
  repeat rw [Sail.freeM_bind_assoc]
  rw [Sail.early_return_lift_bind, Sail.run_bind_of_ok _ _ _ _ _ read, entry, matched]
  simp [Sail.freeM_pure_bind, SailRV32.Functions.pmpCheckRWX,
    SailRV32.Functions._get_Pmpcfg_ent_R, SailRV32.Functions.pmpLocked,
    SailRV32.Functions._get_Pmpcfg_ent_L, SailRV32.Functions.accessFaultFromAccessType,
    _root_.Sail.BitVec.extractLsb, BitVec.extractLsb]
  rfl

end Tests.SailPMP
