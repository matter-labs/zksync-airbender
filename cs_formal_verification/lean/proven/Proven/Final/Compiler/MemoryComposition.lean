module
public import Proven.Compiler.MemoryComposition
public import Proven.NonVacuous.UnrolledNative.Premises
public import Proven.NonVacuous.PaddedMachines.Boot
public import Proven.NonVacuous.UnifiedBoot
public import Proven.NonVacuous.NativeMachines

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler
open Trace Trace.Machine NativeMemory

/-- The address classes split the single RAM permutation of an unrolled trace into its three relations. -/
theorem unrolled_memory_composition : UnrolledMemoryCompositionClaim := by
  intro config trace workers initial cells program layout inits boot callers machine production
  exact (production_iff trace workers unrolledCaller (fun row => Delegation.Requests.caller row.assignment)
    Delegation.Caller.machinePorts (boot_architectural boot)
    (fun row member => unrolled_row_classes row (fun selected => callers row (List.mem_filter.mpr ⟨member, selected⟩))
      (machine row member))).mp production

/-- The address classes split the single RAM permutation of a unified trace into its three relations. -/
theorem unified_memory_composition : UnifiedMemoryCompositionClaim := by
  intro config trace workers initial cells program layout inits boot callers machine production
  exact (production_iff trace workers unifiedCaller (fun row => UnifiedReduced.Caller.request row.assignment)
    UnifiedReduced.Caller.machinePorts (boot_architectural boot)
    (fun row member => unified_row_classes row (callers row member) (machine row member))).mp production

/-- The one-row ADD trace meets the unrolled premises: its three relations give the single RAM permutation. -/
theorem unrolled_memory_composition_satisfiable : UnrolledMemoryCompositionSatisfiableClaim := by
  have boot := NonVacuous.UnrolledNative.boot .unrolledFullUnsigned (Or.inl rfl)
  have ordinary : ∀ row ∈ NonVacuous.UnrolledNative.trace.rows, unrolledCaller row = false := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    decide +kernel
  have machine : ∀ row ∈ NonVacuous.UnrolledNative.trace.rows, ∀ port ∈ Delegation.Caller.machinePorts row,
      Architectural (port.address.code row.assignment) := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    exact ports_architectural (by decide +kernel)
  have callers : ∀ row ∈ unrolledCallers NonVacuous.UnrolledNative.trace,
      ∃ (before : RV.State) (callers : List Delegation.Caller.RVProgramEntry),
        Delegation.Caller.RVBinding row.assignment before callers := by
    intro row member
    obtain ⟨present, selected⟩ := List.mem_filter.mp member
    exact absurd selected (by simp [ordinary row present])
  refine ⟨.unrolledFullUnsigned, NonVacuous.UnrolledNative.trace, NonVacuous.Machine.workers,
    NonVacuous.PooledBoot.initial, NonVacuous.PooledBoot.cells, NonVacuous.UnrolledNative.program,
    InitsTeardowns.importedLayout, NonVacuous.PooledBoot.inits, rfl, boot, callers, machine, ?_⟩
  exact (production_iff _ _ unrolledCaller (fun row => Delegation.Requests.caller row.assignment)
    Delegation.Caller.machinePorts (boot_architectural boot)
    (fun row member => unrolled_row_classes row (fun selected => callers row (List.mem_filter.mpr ⟨member, selected⟩))
      (machine row member))).mpr
    ⟨NonVacuous.UnrolledNative.states, NonVacuous.UnrolledNative.requests, NonVacuous.UnrolledNative.memory⟩

/-- The one-row unified ADD trace meets the unified premises: its three relations give the single RAM permutation. -/
theorem unified_memory_composition_satisfiable : UnifiedMemoryCompositionSatisfiableClaim := by
  have boot := NonVacuous.PaddedMachines.unified_boot
  have ordinary : ∀ row ∈ NonVacuous.UnifiedBoot.trace.rows, ¬ UnifiedReduced.Caller.Selected row.assignment := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    decide +kernel
  have machine : ∀ row ∈ NonVacuous.UnifiedBoot.trace.rows, ∀ port ∈ UnifiedReduced.Caller.machinePorts row,
      Architectural (port.address.code row.assignment) := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    exact ports_architectural (by decide +kernel)
  have callers : ∀ row ∈ NonVacuous.UnifiedBoot.trace.rows, UnifiedReduced.Caller.Selected row.assignment →
      ∃ (before : RV.State) (callers : List Delegation.Caller.RVProgramEntry),
        UnifiedReduced.Caller.RVBinding row.assignment before callers := fun row member selected =>
    absurd selected (ordinary row member)
  refine ⟨.unified, NonVacuous.UnifiedBoot.trace, NonVacuous.Machine.workers, NonVacuous.UnifiedBoot.initial,
    NonVacuous.UnifiedBoot.cells, NonVacuous.PaddedMachines.unifiedProgram, InitsTeardowns.unifiedLayout,
    NonVacuous.UnifiedBoot.inits, List.cons_ne_nil _ _, boot, callers, machine, ?_⟩
  refine (production_iff _ _ unifiedCaller (fun row => UnifiedReduced.Caller.request row.assignment)
    UnifiedReduced.Caller.machinePorts (boot_architectural boot)
    (fun row member => unified_row_classes row (callers row member) (machine row member))).mpr
    ⟨NonVacuous.UnifiedBoot.accepted.states, ?_, ?_⟩
  · change Delegation.Requests.Matching [] []
    exact List.Perm.refl _
  · change ((registerSeeds ++ _) ++ (NonVacuous.UnifiedBoot.row.writes ++ [])).Perm
      ((NonVacuous.UnifiedBoot.registerTerminal ++ _) ++ (NonVacuous.UnifiedBoot.row.reads ++ []))
    exact NonVacuous.UnifiedBoot.memory_perm _

end Airbender.Compiler
