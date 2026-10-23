import Tests.Platform
import Airbender.Proofs.Sail.VirtualMemory

namespace Tests.AirbenderPlatform
open Airbender.Reference Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

private def configured : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0)
      |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [rv32Region attributes]
      |>.insert .mhartid 0 |>.insert .htif_tohost_base none }

private theorem configuration : FlatMemoryConfiguration configured := by
  constructor
  · simp [configured, Std.ExtDHashMap.get?_insert]
  · simp [configured, Std.ExtDHashMap.get?_insert]
  · exact ⟨0x40000100, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0x10, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · simp [configured, Std.ExtDHashMap.get?_insert]
  · exact ⟨Vector.replicate 64 0, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨attributes, by simp [configured, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩
  · exact ⟨0, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · simp [configured]; rfl

namespace Upstream
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform

/-- Preserve the original platform's real CLINT classification. -/
theorem clint_is_device :
    Sail.run (SailRV32.Functions.within_clint (.Physaddr 33554432) 4) configured =
      .ok true configured := by
  have hart : configured.regs.get? .mhartid = some (0 : BitVec 32) := by
    simp [configured, Std.ExtDHashMap.get?_insert]
  have enabled : (MemoryPlatform.devices (ue := SailRV32.exception)).haveClint = true := rfl
  simp only [SailRV32.Functions.within_clint, SailRV32.Functions.plat_have_clint,
    enabled, SailRV32.not, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [Sail.run_bind_of_ok _ _ _ _ _ (read_register hart)]
  rfl

theorem sig_is_device :
    SailRV32.Functions.within_sig (.Physaddr 201326592) 4 = pure true := rfl

end Upstream

namespace Native
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

/-- Disabled device routing is independent of register/memory initialization. -/
theorem clint_is_ram (address : SailRV32.physaddr) (width : Nat) :
    SailRV32.Functions.within_clint address width = pure false := by
  cases address
  rfl

theorem sig_is_ram (address : SailRV32.physaddr) (width : Nat) :
    SailRV32.Functions.within_sig address width = pure false := by
  cases address
  rfl

/-- The disputed region reaches an actual initialized runtime RAM word. -/
theorem clint_checked_load :
    Sail.run (SailRV32.Functions.checked_mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr 33554432) 4 false false false false)
      (wordWriteState configured 33554432 7) =
        .ok (.Ok ((7 : BitVec 32), ())) (wordWriteState configured 33554432 7) := by
  exact checked_word_read_platform
    (before := wordWriteState configured 33554432 7) (address := 33554432) (value := 7)
    (configuration_word_write configuration _ _) (by decide)
    (ordinaryWordAddress_airbender _) (written_word_read _ _ _)

/-- Simple Interrupt Generator (SIG) addresses also retain ordinary RAM writes under Airbender. -/
theorem sig_checked_store :
    Sail.run (SailRV32.Functions.checked_mem_write (.Physaddr 201326592) 4 9
      (.Store .Data) .PBMT_PMA .Machine () false false false) configured =
        .ok (.Ok true) (wordWriteState configured 201326592 9) := by
  exact checked_word_write_platform (before := configured) (address := 201326592)
    configuration (by decide) (ordinaryWordAddress_airbender _) 9

end Native
end Tests.AirbenderPlatform
