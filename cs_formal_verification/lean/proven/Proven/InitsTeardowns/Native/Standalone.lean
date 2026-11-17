module
public import Human.Circuits.InitsTeardowns.Native.Standalone
public import Proven.InitsTeardowns.Native.Emit
public import Proven.InitsTeardowns.Native.Products
public import Proven.InitsTeardowns.Native.Satisfiable
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.InitsTeardowns.Native.Proofs.Standalone
open Trace

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

/-- Native initialization tokens equal the boot interface tokens for the same checked public windows. -/
theorem init_tokens {E : Type} [CommRing E]
    (parameters : Parameters babyBearModulus E) (raw : Raw babyBearModulus)
    (w : InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)
    (windows : ∀ set : Fin 8, parameters.windows set.val = w.topBits[set])
    (checked : ∀ top ∈ w.topBits.toList, top < InitsTeardowns.maxTopBit) :
    ramTokens standaloneArtifact.layout parameters raw .initial = w.initTokens := by
  unfold ramTokens Layout.leaves InitsTeardowns.Witness.initTokens InitsTeardowns.initTokens
  rw [vector_list, List.flatMap_map, List.flatMap_map]
  change (List.finRange 8).flatMap _ = (List.finRange 8).flatMap _
  apply InitsTeardowns.Proofs.flatMap_congr_mem
  intro set member
  clear member
  change (List.finRange 16777216).map _ = (List.range 16777216).map _
  rw [← finRange_values, List.map_map]
  apply List.map_congr_left
  intro row member
  clear member
  have topBound := checked (w.topBits[set]) (by
    rw [vector_list]
    exact List.mem_map.mpr ⟨set, List.mem_finRange set, rfl⟩)
  change (⟨Nat.pair 1 (Nat.pair (addressLo row.val)
    (row.val / 16384 + parameters.windows set.val * 1024)), (0, 0), Nat.pair 0 0⟩ : MemoryToken babyBearModulus) = _
  rw [windows]
  unfold InitsTeardowns.initToken
  congr 1
  exact (native_address (layout := InitsTeardowns.importedLayout) ⟨rfl, Or.inr rfl⟩ topBound row.isLt).symm

/-- Native scalar memory columns have the imported logical teardown variable IDs. -/
theorem columns_binding : ∀ set : Fin 8,
    standaloneArtifact.layout.columns[set].timeLo + 0 = InitsTeardowns.importedLayout.sets[set].timestamp[0] ∧
    standaloneArtifact.layout.columns[set].timeHi + 0 = InitsTeardowns.importedLayout.sets[set].timestamp[1] ∧
    standaloneArtifact.layout.columns[set].valueLo + 0 = InitsTeardowns.importedLayout.sets[set].value[0] ∧
    standaloneArtifact.layout.columns[set].valueHi + 0 = InitsTeardowns.importedLayout.sets[set].value[1] := by
  decide +kernel

/-- Native teardown tokens equal the boot interface tokens at the imported memory placements. -/
theorem teardown_tokens {E : Type} [CommRing E]
    (parameters : Parameters babyBearModulus E)
    (w : InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)
    (windows : ∀ set : Fin 8, parameters.windows set.val = w.topBits[set])
    (checked : ∀ top ∈ w.topBits.toList, top < InitsTeardowns.maxTopBit) :
    ramTokens standaloneArtifact.layout parameters (memoryBank 0 w) .terminal = w.teardownTokens := by
  unfold ramTokens Layout.leaves InitsTeardowns.Witness.teardownTokens
  rw [vector_zip_array, List.flatMap_map, List.flatMap_map]
  change (List.finRange 8).flatMap _ = (List.finRange 8).flatMap _
  apply InitsTeardowns.Proofs.flatMap_congr_mem
  intro set member
  clear member
  change (List.finRange 16777216).map _ = (List.range 16777216).map _
  rw [← finRange_values, List.map_map]
  apply List.map_congr_left
  intro row member
  clear member
  have topBound := checked (w.topBits[set]) (by
    rw [vector_list]
    exact List.mem_map.mpr ⟨set, List.mem_finRange set, rfl⟩)
  have columns := columns_binding set
  change (⟨Nat.pair 1 (Nat.pair (addressLo row.val)
    (row.val / 16384 + parameters.windows set.val * 1024)),
    (w.assignment row.val (standaloneArtifact.layout.columns[set].timeLo + 0),
      w.assignment row.val (standaloneArtifact.layout.columns[set].timeHi + 0)),
    Nat.pair (w.assignment row.val (standaloneArtifact.layout.columns[set].valueLo + 0)).val
      (w.assignment row.val (standaloneArtifact.layout.columns[set].valueHi + 0)).val⟩ : MemoryToken babyBearModulus) = _
  rw [windows, columns.1, columns.2.1, columns.2.2.1, columns.2.2.2]
  unfold InitsTeardowns.teardownToken
  congr 1
  exact (native_address (layout := InitsTeardowns.importedLayout) ⟨rfl, Or.inr rfl⟩ topBound row.isLt).symm

/-- Native gate acceptance gives the products of the boot interface tokens. -/
theorem soundness : StandaloneSoundnessClaim := by
  intro E _ parameters w wires windows checked accepted
  rw [← teardown_tokens parameters w windows checked, ← init_tokens parameters (memoryBank 0 w) w windows checked]
  exact ⟨output_token_product parameters _ wires terminal_follows terminal_leaves accepted,
    output_token_product parameters _ wires initial_follows initial_leaves accepted⟩

/-- The zero instance with zero windows meets the native gate premises. -/
theorem satisfiable : StandaloneSatisfiableClaim :=
  ⟨_, ⟨Vector.replicate _ 0, fun _ _ => 0⟩, _, fun _ => by simp, fun _ member => by
    simp only [Vector.toList_replicate, List.mem_replicate] at member
    rw [member.2]
    decide, accepted_unit standaloneArtifact⟩

end Airbender.InitsTeardowns.Native.Proofs.Standalone
