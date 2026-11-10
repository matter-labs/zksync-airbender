module
public import Human.Circuits.Bigint.RVMemory
public import Slop.Bigint.Memory
public import Slop.Bigint.Addresses
public import Slop.Delegation.RVBoundaryInputs
public import Slop.Defs.Circuits.Bigint.Addresses

@[expose] public section

/-! RV twin of `MemorySoundness.addresses_soundness`: the public state is an `RV.State` (RAM cells include read-write
    shadow RAM below `ROM_END`); pointer bounds come from the state-free seed facts of its initialization. -/

namespace Airbender.Bigint.Memory.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem rv_addresses_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 32 * (-62914560 : ZMod p) = 1) (data : Delegation.MemoryData p)
    (before : RV.State) (cells : List Cell) :
    (circuitModel data).SoundnessUnder (RVInterfaceAssumptions data before cells) Addresses.spec := by
  intro input output w ⟨inputs, accepted, mapping⟩
  have rules := Bigint.Proofs.memory_rules (by omega) accepted inputs.families inputs.table
  have bounds (i : Fin 19) :
      (readToken w importedConstraintsMemoryPorts[i]).word.Bounded := by
    apply Delegation.SeedProofs.read_value_bounds (by norm_num [timestampBase]; omega)
      accepted inputs.publicState.toRVBoundaryInputs.toSeed rules mapping.member
    change importedConstraintsMemoryPorts[i] ∈ importedConstraintsMemoryPorts
    exact Array.getElem_mem i.isLt
  have left := bounds 0
  have right := bounds 9
  simp only [Trace.Proofs.read_word] at left right
  have localBounds : Addresses.InterfaceAssumptions input output w := by
    constructor
    · simpa [mapping.words.left, importedConstraintsMemoryPorts, WordColumns.evaluate] using left
    · simpa [mapping.words.right, importedConstraintsMemoryPorts, WordColumns.evaluate] using right
  have holds := accepted.constraints _ mapping.member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints data.setup.bigint) at holds
  rw [inputs.table] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints setupTable) importedConstraintsTimestampLookups)
  exact Addresses.Proofs.soundness hp inverse input output w ⟨localBounds, core, mapping.words⟩

end Airbender.Bigint.Memory.Proofs
