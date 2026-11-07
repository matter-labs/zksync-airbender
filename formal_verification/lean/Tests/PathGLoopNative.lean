import Tests.PathGLoopNativeBase
import Tests.PathGLoopCPU.Equations
import Tests.PathGLoopNativeQueries

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
set_option warningAsError true
set_option Elab.async false

/- Actual native acceptance assembled from independently proved CPU equations,
   core queries, timestamps, decoding, request matching and memory matching. -/

private theorem machine_core (variant : Variant) (index : Fin 228) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (machineAssignment variant index))
      (UnifiedReduced.importedConstraints (data variant).machine.rom) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  exact ⟨machine_equations variant index (data variant).machine.rom,
    machine_queries variant index⟩

private theorem worker_core (variant : Variant) (index : Fin 56) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (workerAssignment variant index))
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  exact ⟨worker_equations variant index, worker_queries variant index⟩

/-- Exact family dispatch retains the real richer machine list, including
all8 clock lookups in addition to all129 equations and all18 core queries. -/
private theorem machine_constraints (variant : Variant) (index : Fin 228) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (machineAssignment variant index))
      ((⟨.machine, machineAssignment variant index⟩ : Row babyBearModulus UnifiedFamily).constraints
        (data variant).machine.rom) := by
  change FlatOperation.ConstraintsHoldFlat (Verification.environment (machineAssignment variant index))
    (UnifiedReduced.clockConstraints (data variant).machine.rom)
  exact Verification.holds_append (machine_core variant index) (machine_timestamps variant index)

/-- The concrete modeled-setup projection is definitionally the same actual G
setup used by worker_core; no Inputs.tables premise is supplied here. -/
private theorem worker_constraints (variant : Variant) (index : Fin 56) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (workerAssignment variant index))
      ((⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).constraints
        (data variant).workers.setup) := by
  change FlatOperation.ConstraintsHoldFlat (Verification.environment (workerAssignment variant index))
    (Blake2G.clockConstraints (Blake2G.setupTable Blake2G.Control.controllerRows))
  exact Verification.holds_append (worker_core variant index) (worker_timestamps variant index)

/-- The raw imported participation and caller selector stay attached to the
same family/assignment constructor that supplies all machine constraints. -/
private theorem machine_profile (variant : Variant) (index : Fin 228) :
    (⟨.machine, machineAssignment variant index⟩ : Row babyBearModulus UnifiedFamily).family = .machine ∧
      (⟨.machine, machineAssignment variant index⟩ : Row babyBearModulus UnifiedFamily).assignment
        (⟨.machine, machineAssignment variant index⟩ : Row babyBearModulus UnifiedFamily).columns.execute = 1 ∧
      (UnifiedReduced.Caller.Selected (machineAssignment variant index) ↔ isCaller index = true) := by
  exact ⟨rfl, machine_active variant index, native_selected_iff variant index⟩

/-- Raw native G execute column0 is1 for every actual worker. The column ID
is checked by definitional reduction of the imported family metadata. -/
private theorem worker_profile (variant : Variant) (index : Fin 56) :
    (⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).family = .blakeG ∧
      (⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).assignment
        (⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).columns.execute = 1 := by
  refine ⟨rfl, ?_⟩
  change workerAssignment variant index 0 = 1
  simp [workerAssignment]

/-- All seven request-check fields for the same228 CPU/56G candidates. Native
constraints/queries, exact PC/clock chain, public decoding and request
multiplicity are proved outright; architectural matching stays separate. -/
theorem checks (variant : Variant) : UnifiedReduced.Caller.RequestChecks (data variant) := by
  constructor
  · intro row member
    change row ∈ machineRows variant at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact machine_constraints variant index
  · intro row member
    change row ∈ machineRows variant at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact (machine_profile variant index).2.1
  · exact machine_states variant
  · exact caller_decoded variant
  · intro row member
    change row ∈ workerRows variant at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact worker_constraints variant index
  · intro row member
    change row ∈ workerRows variant at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact (worker_profile variant index).2
  · exact request_matching variant

/-- Outright native acceptance for each concrete variant. This does not assert
Sail execution or assume Inputs, desired reads/results, or memory matching. -/
theorem accepted (variant : Variant) :
    UnifiedReduced.Caller.MixedMemoryAccepted (data variant) (ordinaryProgram variant) := by
  exact ⟨checks variant, ordinary_decoded variant, memory_matching variant⟩

end Tests.PathGLoopNative
