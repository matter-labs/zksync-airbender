import Slop.Sail.FlatMemory

namespace Tests.SailFlatMemory
open Airbender.Reference Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true

private def configured : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .mstatus 0
      |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10 }

-- Check the complete generated translator, including its environment queries.
-- The top RV32 word address must remain intact in the 34-bit physical address.
theorem high_address_load  :
    Sail.run (SailRV32.Functions.translateAddr (.Virtaddr 0xfffffffc) (.Load .Data) .Machine)
      configured = .ok (.Ok (.Physaddr 0xfffffffc, .PBMT_PMA, ())) configured := by
  apply machine_translate_address (isa := 0x40000100) (supervisor := 0) (machine := 0x10)
  all_goals first | exact Or.inl rfl | simp [configured, Std.ExtDHashMap.get?_insert]

theorem code_fetch  :
    Sail.run (SailRV32.Functions.translateAddr (.Virtaddr 16) (.InstructionFetch ()) .Machine)
      configured = .ok (.Ok (.Physaddr 16, .PBMT_PMA, ())) configured := by
  apply machine_translate_address (isa := 0x40000100) (supervisor := 0) (machine := 0x10)
  all_goals first | exact Or.inr (Or.inr rfl) | simp [configured, Std.ExtDHashMap.get?_insert]

theorem uninitialized_access_rejected : ∃ error,
    Sail.run (SailRV32.Functions.default_access_info (.Load .Data)) (default : State) =
      .error error (default : State) := by
  have missing : Sail.run (SailRV32.readReg .mstatus) (default : State) =
      .error .Unreachable (default : State) := by
    have absent : (default : State).regs.get? .mstatus = none := by
      change (Std.ExtDHashMap.emptyWithCapacity :
        Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType).get? .mstatus = none
      simp
    dsimp [Sail.run, SailRV32.readReg, PreSail.readReg, interpretSailEffects,
      FreeM.liftM, interpretInstructionEffect]
    simp [absent]
    rfl
  simp only [SailRV32.Functions.default_access_info]
  exact ⟨_, Sail.run_bind_of_error _ _ _ _ _ missing⟩

end Tests.SailFlatMemory
