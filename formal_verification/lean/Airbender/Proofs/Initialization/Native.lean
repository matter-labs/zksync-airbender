import Airbender.Review.Circuits.Initialization.Artifact
import Airbender.Proofs.Initialization.Products

namespace Airbender.Initialization.Proofs
set_option warningAsError true
set_option Elab.async false

prove_ram_initialization_wiring standalone_terminal_follows standalone_initial_follows
  for standalone from "../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json"

prove_ram_initialization_wiring unified_terminal_follows unified_initial_follows
  for unified from "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json" unified_inline

theorem standalone_terminal_leaves :
    standalone.terminal.leaves = standalone.layout.leaves .terminal := by decide +kernel

theorem standalone_initial_leaves :
    standalone.initial.leaves = standalone.layout.leaves .initial := by decide +kernel

theorem unified_terminal_leaves :
    unified.terminal.leaves = unified.layout.leaves .terminal := by decide +kernel

theorem unified_initial_leaves :
    unified.initial.leaves = unified.layout.leaves .initial := by decide +kernel

variable {p : Nat} [Fact p.Prime] [CommRing E]

theorem standalone_terminal_tokens (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (accepted : Accepted standalone parameters raw wires)
    (row : Fin standalone.layout.rows) :
    wires standalone.terminal.output row.val =
      ((standalone.layout.leaves .terminal).map fun leaf =>
        parameters.encode (leaf.token standalone.layout parameters raw row.val)).prod :=
  root_tokens parameters raw wires standalone_terminal_follows standalone_terminal_leaves accepted row

theorem standalone_initial_tokens (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (accepted : Accepted standalone parameters raw wires)
    (row : Fin standalone.layout.rows) :
    wires standalone.initial.output row.val =
      ((standalone.layout.leaves .initial).map fun leaf =>
        parameters.encode (leaf.token standalone.layout parameters raw row.val)).prod :=
  root_tokens parameters raw wires standalone_initial_follows standalone_initial_leaves accepted row

theorem unified_terminal_tokens (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (accepted : Accepted unified parameters raw wires)
    (row : Fin unified.layout.rows) :
    wires unified.terminal.output row.val =
      ((unified.layout.leaves .terminal).map fun leaf =>
        parameters.encode (leaf.token unified.layout parameters raw row.val)).prod :=
  root_tokens parameters raw wires unified_terminal_follows unified_terminal_leaves accepted row

theorem unified_initial_tokens (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (accepted : Accepted unified parameters raw wires)
    (row : Fin unified.layout.rows) :
    wires unified.initial.output row.val =
      ((unified.layout.leaves .initial).map fun leaf =>
        parameters.encode (leaf.token unified.layout parameters raw row.val)).prod :=
  root_tokens parameters raw wires unified_initial_follows unified_initial_leaves accepted row

theorem standalone_products (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (accepted : Accepted standalone parameters raw wires) :
    rootProduct standalone standalone.terminal wires =
        ((ramTokens standalone.layout parameters raw .terminal).map parameters.encode).prod ∧
      rootProduct standalone standalone.initial wires =
        ((ramTokens standalone.layout parameters raw .initial).map parameters.encode).prod :=
  ⟨output_token_product parameters raw wires standalone_terminal_follows standalone_terminal_leaves accepted,
    output_token_product parameters raw wires standalone_initial_follows standalone_initial_leaves accepted⟩

theorem unified_products (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (accepted : Accepted unified parameters raw wires) :
    rootProduct unified unified.terminal wires =
        ((ramTokens unified.layout parameters raw .terminal).map parameters.encode).prod ∧
      rootProduct unified unified.initial wires =
        ((ramTokens unified.layout parameters raw .initial).map parameters.encode).prod :=
  ⟨output_token_product parameters raw wires unified_terminal_follows unified_terminal_leaves accepted,
    output_token_product parameters raw wires unified_initial_follows unified_initial_leaves accepted⟩

end Airbender.Initialization.Proofs
