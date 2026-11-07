import Airbender.Proofs.Sail.PMA

namespace Tests.SailPMA
open Airbender.Reference Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

private def configured (regions : List SailRV32.PMA_Region) : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .pma_regions regions }

theorem upper_word :
    Sail.run (SailRV32.Functions.pmaCheck (.Physaddr 0xfffffffc) 4 (.Load .Data) .PBMT_PMA false)
      (configured [rv32Region attributes]) =
      .ok (.Ok ⟨.CannotSplit, 0⟩) (configured [rv32Region attributes]) := by
  apply pma_word_access (address := 0xfffffffc) (attributes := attributes)
  all_goals first | exact Or.inl rfl | decide | simp [configured, attributes]

theorem store_word :
    Sail.run (SailRV32.Functions.pmaCheck (.Physaddr 4194304) 4 (.Store .Data) .PBMT_PMA false)
      (configured [rv32Region attributes]) =
      .ok (.Ok ⟨.CannotSplit, 0⟩) (configured [rv32Region attributes]) := by
  apply pma_word_access (address := 4194304) (attributes := attributes)
  all_goals first | exact Or.inr (Or.inl rfl) | decide | simp [configured, attributes]

theorem no_region_rejects :
    Sail.run (SailRV32.Functions.pmaCheck (.Physaddr 4194304) 4 (.Load .Data) .PBMT_PMA false)
      (configured []) = .ok (.Err (.E_Load_Access_Fault ())) (configured []) := by
  have initialized : (configured []).regs.get? .pma_regions = some [] := by simp [configured]
  simp only [SailRV32.Functions.pmaCheck, SailRV32.SailME.run]
  repeat rw [Sail.freeM_bind_assoc]
  rw [Sail.early_return_lift_bind, Sail.run_bind_of_ok _ _ _ _ _ (read_register initialized)]
  simp [SailRV32.Functions.matching_pma_region, SailRV32.Functions.matching_pma_region_bits_range,
    SailRV32.Functions.accessFaultFromAccessType, Sail.freeM_pure_bind]
  rfl

end Tests.SailPMA
