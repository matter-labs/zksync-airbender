module
public import Human.Circuits.InitsTeardowns.Native.Unified
public import Proven.InitsTeardowns.Native.Emit
public import Proven.InitsTeardowns.Native.Products
public import Proven.InitsTeardowns.Native.Satisfiable
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.InitsTeardowns.Native.Proofs.Unified
open Trace

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

/-- Native initialization tokens equal the boot interface tokens for the same checked public windows. -/
theorem init_tokens {E : Type} [CommRing E]
    (parameters : Parameters babyBearModulus E) (raw : Raw babyBearModulus)
    (w : InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)
    (windows : ∀ set : Fin 2, parameters.windows set.val = w.topBits[set])
    (checked : ∀ top ∈ w.topBits.toList, top < InitsTeardowns.maxTopBit) :
    ramTokens unifiedArtifact.layout parameters raw .initial = w.initTokens := by
  unfold ramTokens Layout.leaves InitsTeardowns.Witness.initTokens InitsTeardowns.initTokens
  rw [vector_list, List.flatMap_map, List.flatMap_map]
  change (List.finRange 2).flatMap _ = (List.finRange 2).flatMap _
  apply InitsTeardowns.Proofs.flatMap_congr_mem
  intro set member
  clear member
  change (List.finRange 8388608).map _ = (List.range 8388608).map _
  rw [← finRange_values, List.map_map]
  apply List.map_congr_left
  intro row member
  clear member
  have topBound := checked (w.topBits[set]) (by
    rw [vector_list]
    exact List.mem_map.mpr ⟨set, List.mem_finRange set, rfl⟩)
  change (⟨Nat.pair 1 (Nat.pair (addressLo row.val)
    (row.val / 16384 + parameters.windows set.val * 512)), (0, 0), Nat.pair 0 0⟩ : MemoryToken babyBearModulus) = _
  rw [windows]
  unfold InitsTeardowns.initToken
  congr 1
  exact (native_address (layout := InitsTeardowns.unifiedLayout) ⟨rfl, Or.inl rfl⟩ topBound row.isLt).symm

/-- Native scalar memory columns have the imported logical teardown variable IDs. -/
theorem columns_binding : ∀ set : Fin 2,
    unifiedArtifact.layout.columns[set].timeLo + 96 = InitsTeardowns.unifiedLayout.sets[set].timestamp[0] ∧
    unifiedArtifact.layout.columns[set].timeHi + 96 = InitsTeardowns.unifiedLayout.sets[set].timestamp[1] ∧
    unifiedArtifact.layout.columns[set].valueLo + 96 = InitsTeardowns.unifiedLayout.sets[set].value[0] ∧
    unifiedArtifact.layout.columns[set].valueHi + 96 = InitsTeardowns.unifiedLayout.sets[set].value[1] := by
  decide +kernel

/-- Native teardown tokens equal the boot interface tokens at the imported memory placements. -/
theorem teardown_tokens {E : Type} [CommRing E]
    (parameters : Parameters babyBearModulus E)
    (w : InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)
    (windows : ∀ set : Fin 2, parameters.windows set.val = w.topBits[set])
    (checked : ∀ top ∈ w.topBits.toList, top < InitsTeardowns.maxTopBit) :
    ramTokens unifiedArtifact.layout parameters (rawOfWitness 96 w) .terminal = w.teardownTokens := by
  unfold ramTokens Layout.leaves InitsTeardowns.Witness.teardownTokens
  rw [vector_zip_array, List.flatMap_map, List.flatMap_map]
  change (List.finRange 2).flatMap _ = (List.finRange 2).flatMap _
  apply InitsTeardowns.Proofs.flatMap_congr_mem
  intro set member
  clear member
  change (List.finRange 8388608).map _ = (List.range 8388608).map _
  rw [← finRange_values, List.map_map]
  apply List.map_congr_left
  intro row member
  clear member
  have topBound := checked (w.topBits[set]) (by
    rw [vector_list]
    exact List.mem_map.mpr ⟨set, List.mem_finRange set, rfl⟩)
  have columns := columns_binding set
  change (⟨Nat.pair 1 (Nat.pair (addressLo row.val)
    (row.val / 16384 + parameters.windows set.val * 512)),
    (w.assignment row.val (unifiedArtifact.layout.columns[set].timeLo + 96),
      w.assignment row.val (unifiedArtifact.layout.columns[set].timeHi + 96)),
    Nat.pair (w.assignment row.val (unifiedArtifact.layout.columns[set].valueLo + 96)).val
      (w.assignment row.val (unifiedArtifact.layout.columns[set].valueHi + 96)).val⟩ : MemoryToken babyBearModulus) = _
  rw [windows, columns.1, columns.2.1, columns.2.2.1, columns.2.2.2]
  unfold InitsTeardowns.teardownToken
  congr 1
  exact (native_address (layout := InitsTeardowns.unifiedLayout) ⟨rfl, Or.inl rfl⟩ topBound row.isLt).symm

end Airbender.InitsTeardowns.Native.Proofs.Unified
