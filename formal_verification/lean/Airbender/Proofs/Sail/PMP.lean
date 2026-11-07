import Airbender.Proofs.Sail.FlatMemory

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- The pinned zero-grain PMP platform reads each actual initialized address
    without masking it. Entry permissions remain a separate check. -/
theorem pmp_read_address {before : State} {entries : Vector (BitVec 8) 64}
    {addresses : Vector (BitVec 32) 64}
    (config : before.regs.get? .pmpcfg_n = some entries)
    (initialized : before.regs.get? .pmpaddr_n = some addresses) (index : Fin 64) :
    run (SailRV32.Functions.pmpReadAddrReg index.val) before =
      .ok addresses[index] before := by
  simp only [SailRV32.Functions.pmpReadAddrReg]
  rw [run_bind_of_ok _ _ _ _ _ (read_register config)]
  simp only [freeM_pure_bind]
  rw [run_bind_of_ok _ _ _ _ _ (read_register initialized)]
  simp [SailRV32.Functions.sys_pmp_grain, index.isLt]
  split <;> rfl

theorem pmp_match_off (address : SailRV32.physaddr) (width : BitVec 32)
    (current previous : BitVec 32) :
    SailRV32.Functions.pmpMatchAddr address width 0 current previous = pure .PMP_NoMatch := by
  cases address
  rfl

private theorem pmp_read_bind {α : Type} {before : State}
    {entries : Vector (BitVec 8) 64} {addresses : Vector (BitVec 32) 64} {index : Nat}
    (config : before.regs.get? .pmpcfg_n = some entries)
    (initialized : before.regs.get? .pmpaddr_n = some addresses)
    (bound : index < 64) (next : BitVec 32 → SailRV32.SailM α) :
    run (SailRV32.Functions.pmpReadAddrReg index >>= next) before =
      run (next addresses[index]) before :=
  run_bind_of_ok _ _ _ _ _ (pmp_read_address config initialized ⟨index, bound⟩)

private theorem config_zero (index : Int) (bound : index.toNat < 64) :
    (Vector.replicate 64 (0 : BitVec 8))[index]'bound = 0 := by
  change (Vector.replicate 64 (0 : BitVec 8))[index.toNat] = 0
  simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The original sixteen-entry PMP walk permits Machine accesses when every
    entry is Off. Its initialized address registers can contain arbitrary data. -/
theorem machine_pmp_off {before : State} {addresses : Vector (BitVec 32) 64}
    (config : before.regs.get? .pmpcfg_n = some (Vector.replicate 64 0))
    (initialized : before.regs.get? .pmpaddr_n = some addresses)
    (address : SailRV32.physaddr) (width : Nat)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload) :
    run (SailRV32.Functions.pmpCheck address width access .Machine) before =
      .ok none before := by
  simp only [SailRV32.Functions.pmpCheck, SailRV32.Functions.sys_pmp_count,
    show ((16 : Int) == 0) = false from rfl, Bool.false_eq_true, ite_false,
    forIn_eq_forIn', SailRV32.SailME.run, freeM_pure_bind]
  dsimp only [ForIn'.forIn', IntRange.forIn']
  rw [IntRange.forIn'.loop]
  norm_num [Membership.mem, IntRange.instMemIntRange]
  repeat rw [freeM_bind_assoc]
  rw [early_return_lift_bind]
  rw [run_bind_of_ok _ _ _ _ _ (read_register config)]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | (rw [pmp_read_bind config initialized] <;> try omega)
    | rw [run_bind_of_ok _ _ _ _ _ (read_register config)]
    | rw [config_zero]
    | rw [pmp_match_off]
    | simp [freeM_pure_bind]
    | (rw [IntRange.forIn'.loop]; norm_num [Membership.mem, IntRange.instMemIntRange])
  rfl

end Airbender.Reference.RiscV.Sail
