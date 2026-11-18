module
public import Proven.NonVacuous.UnrolledNative.Model
public import Proven.NonVacuous.NativeMachines

@[expose] public section
namespace Airbender.NonVacuous.UnrolledNative
open Trace Trace.Machine Arithmetic Compiler NativeArithmetic
set_option warningAsError true

/-- The ADD metadata fits the native decoder and has zero omitted coordinates. -/
theorem tables_bound : NativePublicSetup.Bound PooledBoot.initial program tables := by
  constructor
  · rfl
  · decide +kernel
  · intro candidate member
    obtain rfl := List.mem_singleton.mp member
    left
    decide +kernel
  · intro candidate member index omitted
    obtain rfl := List.mem_singleton.mp member
    have checked : ∀ index : Fin 9,
        (NativeLookups.circuitFor entry.data.family).decode_table_columns_mask[index.val]?.getD false = false →
          (entry.data.row entry.pc)[index] = 0 := by decide +kernel
    exact checked index omitted

/-- Window zero contains all aligned ROM words in the native standalone word table. -/
theorem covers_rom : NativePublicSetup.CoversROM PooledBoot.cells := by
  intro index
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨0, by decide +kernel, List.mem_map.mpr ⟨index.val, ?_, ?_⟩⟩
  · change index.val ∈ List.range 16777216
    rw [List.mem_range]
    have bounded := index.isLt
    omega
  · have address : InitsTeardowns.windowAddress InitsTeardowns.importedLayout 0 index.val = 4 * index.val := by
      rw [InitsTeardowns.windowAddress,
        show InitsTeardowns.importedLayout.wordBits = 2 from rfl,
        show InitsTeardowns.importedLayout.traceLog = 24 from rfl]
      simp [Nat.mul_comm]
    exact congrArg (fun address => Cell.ram (BitVec.ofNat 32 address)) address

/-- The ADD row and its terminal tuple balance the submitted state argument. -/
theorem states : (trace.initial :: trace.rows.map Row.finish).Perm
    (trace.terminal :: trace.rows.map Row.start) := PooledBoot.accepted.states

/-- The ordinary ADD instruction has no delegation request. -/
theorem requests : Delegation.Requests.Matching
    ((unrolledCallers trace).map fun row => Delegation.Requests.caller row.assignment)
    Machine.workers.fulfillments := by
  change Delegation.Requests.Matching [] []
  exact List.Perm.refl _

/-- The ADD register transfers share the complete native RAM seed and terminal domain. -/
theorem memory :
    (trace.initialMemory ++ (unrolledSteps trace ++ Machine.workers.steps).map Prod.snd).Perm
      (trace.terminalMemory ++ (unrolledSteps trace ++ Machine.workers.steps).map Prod.fst) := by
  change ((registerSeeds ++ _) ++ (PooledBoot.row.writes ++ [])).Perm
    ((PooledBoot.registerTerminal ++ _) ++ (PooledBoot.row.reads ++ []))
  exact PooledBoot.memory_perm _

end Airbender.NonVacuous.UnrolledNative
