module
public import Proven.NonVacuous.PaddedMachines.Rows
public import Proven.NonVacuous.PaddedMachines.Boot
public import Proven.Trace.PaddingBoundary
public import Human.Trace.Machine.Padding

@[expose] public section
namespace Airbender.NonVacuous.PaddedMachines
open Trace Trace.Machine Arithmetic PaddingBoundary
set_option warningAsError true

/-- One inactive row and one native ADD row form the full unrolled layout. -/
noncomputable def pooled : PooledTrace babyBearModulus :=
  { UnrolledNative.trace with rows := [pooledPadding, PooledBoot.row] }

/-- One inactive row and one native ADD row form the full unified layout. -/
noncomputable def unified : UnifiedTrace babyBearModulus :=
  { UnifiedBoot.trace with rows := [unifiedPadding, UnifiedBoot.row] }

/-- Participation selects exactly the unrolled ADD trace. -/
theorem pooled_active : active pooled = UnrolledNative.trace := by
  have rows : pooled.rows.filter (fun row => decide (row.assignment row.columns.execute = 1)) =
      [PooledBoot.row] := by kernel_rfl
  unfold active
  rw [rows]
  rfl

/-- Participation selects exactly the unified ADD trace. -/
theorem unified_active : active unified = UnifiedBoot.trace := by
  have rows : unified.rows.filter (fun row => decide (row.assignment row.columns.execute = 1)) =
      [UnifiedBoot.row] := by kernel_rfl
  unfold active
  rw [rows]
  rfl

/-- The complete unrolled layout has two rows, with one participating row and one padding row. -/
theorem pooled_sizes : pooled.rows ≠ [] ∧ pooled.rows.length = 2 ∧
    (active pooled).rows.length = 1 ∧ (inactive pooled).rows.length = 1 :=
  ⟨List.cons_ne_nil _ _, rfl, by kernel_rfl, by kernel_rfl⟩

/-- The complete unified layout has two rows, with one participating row and one padding row. -/
theorem unified_sizes : unified.rows ≠ [] ∧ unified.rows.length = 2 ∧
    (active unified).rows.length = 1 ∧ (inactive unified).rows.length = 1 :=
  ⟨List.cons_ne_nil _ _, rfl, by kernel_rfl, by kernel_rfl⟩

/-- Both imported CPU assignments satisfy their constraints and the complete masked boundary. -/
theorem pooled_layout : AcceptedLayout pooled :=
  Proofs.layout_cons_inactive (Proofs.layout_of_accepted PooledBoot.accepted)
    pooledPadding pooled_padding_inactive pooled_padding_satisfies

/-- Both unified assignments retain every equation and lookup before identity erasure. -/
theorem unified_layout : AcceptedLayout unified :=
  Proofs.layout_cons_inactive (Proofs.layout_of_accepted UnifiedBoot.accepted)
    unifiedPadding unified_padding_inactive unified_padding_satisfies

/-- The empty worker pools meet the full masked worker contract. -/
theorem workers_masked : MaskedWorkersAccepted Machine.workers := by
  constructor <;> intro row member <;> cases member

/-- The full unrolled layout has exact masked state, request and memory matching. -/
theorem pooled_masked : MaskedUnrolledAcceptance pooled Machine.workers UnrolledNative.program := by
  refine ⟨workers_masked, pooled_layout.constraints, pooled_layout.binding.selectors, ?_,
    pooled_layout.binding.states, ?_, ?_⟩
  · simpa only [pooled_active] using pooled_accepted.decoded
  · change ([] : List (Option (MemoryToken babyBearModulus))).Perm []
    exact List.Perm.refl _
  · change (pooled.initialMemory.map some ++ contributions pooled.rows
      (fun row => row.assignment row.columns.execute) Row.writes ++ []).Perm
      (pooled.terminalMemory.map some ++ contributions pooled.rows
        (fun row => row.assignment row.columns.execute) Row.reads ++ [])
    simpa only [List.append_nil] using pooled_layout.binding.memory

/-- The full unified layout has exact masked state, request and memory matching. -/
theorem unified_masked : MaskedUnifiedAcceptance unified Machine.workers unifiedProgram := by
  refine ⟨workers_masked, unified_layout.constraints, unified_layout.binding.selectors, ?_,
    unified_layout.binding.states, ?_, ?_⟩
  · simpa only [unified_active] using unified_accepted.decoded
  · change ([] : List (Option (MemoryToken babyBearModulus))).Perm []
    exact List.Perm.refl _
  · change (unified.initialMemory.map some ++ contributions unified.rows
      (fun row => row.assignment row.columns.execute) Row.writes ++ []).Perm
      (unified.terminalMemory.map some ++ contributions unified.rows
        (fun row => row.assignment row.columns.execute) Row.reads ++ [])
    simpa only [List.append_nil] using unified_layout.binding.memory

end Airbender.NonVacuous.PaddedMachines
