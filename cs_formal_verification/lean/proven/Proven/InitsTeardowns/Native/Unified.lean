module
public import Human.Circuits.InitsTeardowns.Native.Unified
public import Proven.InitsTeardowns.Native.Emit
public import Proven.InitsTeardowns.Native.Products
public import Proven.InitsTeardowns.Native.Satisfiable
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.InitsTeardowns.Native.Proofs.Unified

/-- The extracted graph is bound to the existing imported circuit. -/
theorem binding : UnifiedBindingClaim := by
  unfold UnifiedBindingClaim
  kernel_rfl

prove_ram_product_wiring terminal_follows initial_follows for unifiedArtifact
  from "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json" unified_inline

/-- The teardown tree covers each native set once. -/
theorem terminal_leaves : unifiedArtifact.terminal.leaves = unifiedArtifact.layout.leaves .terminal := by decide +kernel

/-- The initialization tree covers each native set once. -/
theorem initial_leaves : unifiedArtifact.initial.leaves = unifiedArtifact.layout.leaves .initial := by decide +kernel

/-- Native gate acceptance gives both complete token products. -/
theorem soundness : UnifiedSoundnessClaim := by
  intro E _ parameters raw wires accepted
  exact ⟨output_token_product parameters raw wires terminal_follows terminal_leaves accepted,
    output_token_product parameters raw wires initial_follows initial_leaves accepted⟩

/-- The native gate premises have an assignment. -/
theorem satisfiable : UnifiedSatisfiableClaim :=
  ⟨_, _, _, accepted_unit unifiedArtifact⟩

end Airbender.InitsTeardowns.Native.Proofs.Unified
