module
public import Proven.NonVacuous.UnrolledNative.Model
public import Proven.NonVacuous.UnifiedBoot
public import Proven.NonVacuous.NativeMachines

@[expose] public section
namespace Airbender.NonVacuous.PaddedMachines
open Trace Trace.Machine Arithmetic
set_option warningAsError true

/-- The one-row ADD instance supplies the complete unrolled acceptance premises. -/
theorem pooled_accepted : UnrolledAcceptance UnrolledNative.trace Machine.workers UnrolledNative.program := by
  refine ⟨Machine.workers_accepted, ?_, ?_, PooledBoot.accepted.states, ?_, ?_, ?_⟩
  · intro row member
    obtain rfl := List.mem_singleton.mp member
    exact PooledBoot.satisfies
  · intro row member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro row member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨UnrolledNative.entry, List.mem_singleton_self _, rfl, by kernel_rfl⟩
  · change Delegation.Requests.Matching [] []
    exact List.Perm.refl _
  · change ((registerSeeds ++ _) ++ (PooledBoot.row.writes ++ [])).Perm
      ((PooledBoot.registerTerminal ++ _) ++ (PooledBoot.row.reads ++ []))
    exact PooledBoot.memory_perm _

/-- The public unified projection gives the ADD fixture's machine entry. -/
def unifiedEntry : RVMachineProgramEntry :=
  (rvMachineProgramEntryWith .unified UnifiedBoot.initial 0).get (by decide +kernel)

def unifiedProgram : List RVMachineProgramEntry := [unifiedEntry]

/-- Public ROM bytes produce exactly the submitted ADD entry. -/
theorem unified_program_image :
    rvMachineProgramImage .unified UnifiedBoot.initial [0] = some unifiedProgram := by kernel_rfl

/-- Every native register terminal retains one architectural register address. -/
theorem unified_register_addresses : (UnifiedBoot.registerTerminal.map MemoryToken.address).Perm
    (registerCells.map Cell.addressCode) := by decide +kernel

/-- Zero teardown columns retain the exact public inline initialization tokens. -/
theorem unified_teardown_tokens :
    UnifiedBoot.inits.flatMap InitsTeardowns.Witness.teardownTokens =
      UnifiedBoot.inits.flatMap InitsTeardowns.Witness.initTokens := by
  simp only [UnifiedBoot.inits, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact InitsTeardowns.Proofs.teardown_zero _ (fun _ _ => rfl)

/-- The one-row unified fixture has the full public boot and terminal-token contract. -/
theorem unified_boot : BootInputs .unified UnifiedBoot.trace UnifiedBoot.initial UnifiedBoot.cells unifiedProgram
    InitsTeardowns.unifiedLayout UnifiedBoot.inits := by
  refine ⟨UnifiedBoot.cells_facts.1, UnifiedBoot.cells_facts.2, rfl, UnifiedBoot.inputs.registersZero,
    ⟨[0], unified_program_image⟩, UnifiedBoot.topBits_checked, rfl,
    ⟨UnifiedBoot.registerTerminal, unified_register_addresses, ?_⟩, rfl,
    UnifiedBoot.inputs.image, rfl, ?_⟩
  · change UnifiedBoot.registerTerminal ++ UnifiedBoot.inits.flatMap InitsTeardowns.Witness.initTokens = _
    rw [unified_teardown_tokens]
  · exact ⟨⟨4, (8, 0)⟩, rfl, UnifiedBoot.accepted.states⟩

/-- The unified ADD row has every CPU and worker acceptance premise. -/
theorem unified_accepted : UnifiedAcceptance UnifiedBoot.trace Machine.workers unifiedProgram := by
  refine ⟨Machine.workers_accepted, ?_, ?_, UnifiedBoot.accepted.states, ?_, ?_, ?_⟩
  · intro row member
    obtain rfl := List.mem_singleton.mp member
    exact UnifiedBoot.satisfies
  · intro row member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro row member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨unifiedEntry, List.mem_singleton_self _, rfl, by kernel_rfl⟩
  · change Delegation.Requests.Matching [] []
    exact List.Perm.refl _
  · change ((registerSeeds ++ _) ++ (UnifiedBoot.row.writes ++ [])).Perm
      ((UnifiedBoot.registerTerminal ++ _) ++ (UnifiedBoot.row.reads ++ []))
    exact UnifiedBoot.memory_perm _

/-- The public ADD instruction has no special5 call. -/
theorem unified_no_special : NoSpecial5 unifiedProgram := by
  intro candidate member
  obtain rfl := List.mem_singleton.mp member
  change some (RV.Instr.op .add 3 1 2) ≠ some (.delegate .keccak)
  intro impossible
  cases impossible

/-- The ADD fixture contains no external input read. -/
theorem unified_stream_ports : UnifiedStreamPorts UnifiedBoot.trace UnifiedBoot.initial.input := by
  intro row member selected
  obtain rfl := List.mem_singleton.mp member
  have no_read : unifiedIsRead UnifiedBoot.row = false := by kernel_rfl
  rw [no_read] at selected
  cases selected

end Airbender.NonVacuous.PaddedMachines
