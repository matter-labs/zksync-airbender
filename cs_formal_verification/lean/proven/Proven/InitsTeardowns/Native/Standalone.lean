module
public import Human.Circuits.InitsTeardowns.Native.Standalone
public import Proven.InitsTeardowns.Native.Emit
public import Proven.InitsTeardowns.Native.Products
public import Proven.InitsTeardowns.Native.Satisfiable
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.InitsTeardowns.Native.Proofs.Standalone

/-- The extracted graph is bound to the existing imported circuit. -/
theorem binding : StandaloneBindingClaim := by
  unfold StandaloneBindingClaim
  kernel_rfl

prove_ram_product_wiring terminal_follows initial_follows for standaloneArtifact
  from "../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json"

/-- The teardown tree covers each native set once. -/
theorem terminal_leaves : standaloneArtifact.terminal.leaves = standaloneArtifact.layout.leaves .terminal := by decide +kernel

/-- The initialization tree covers each native set once. -/
theorem initial_leaves : standaloneArtifact.initial.leaves = standaloneArtifact.layout.leaves .initial := by decide +kernel

/-- Native gate acceptance gives both complete token products. -/
theorem soundness : StandaloneSoundnessClaim := by
  intro E _ parameters raw wires accepted
  exact ⟨output_token_product parameters raw wires terminal_follows terminal_leaves accepted,
    output_token_product parameters raw wires initial_follows initial_leaves accepted⟩

/-- The native gate premises have an assignment. -/
theorem satisfiable : StandaloneSatisfiableClaim :=
  ⟨_, _, _, accepted_unit standaloneArtifact⟩

end Airbender.InitsTeardowns.Native.Proofs.Standalone
