module
public import Proven.Compiler.DescriptionExtension
public import Proven.Compiler.WorkerBindings.KeccakColumnParity

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerExtension.KeccakColumnParity
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 32768

/-- The complete typed address bank has no repeated physical address. -/
theorem unique : WorkerBindings.KeccakColumnParity.addresses.toList.Nodup := by decide +kernel

/-- The finite bank covers all physical coordinates of the checked arithmetic artifact. -/
def bank : WireBank 202 :=
  WireBank.ofList WorkerBindings.KeccakColumnParity.addresses.toList (by decide)

/-- The bank and the vector use the same physical coordinate. -/
theorem coordinate (index : Fin 202) :
    bank.address index = WorkerBindings.KeccakColumnParity.addresses[index] := by
  exact List.get_eq_getElem.trans (Vector.getElem_toList _)

/-- Each source index is bound to its actual captured physical location. -/
theorem placement_binding : (Captures.KeccakColumnParity.imported.circuit).placement_data.entries.toList =
    List.ofFn (fun index : Fin 167 => (index.val, bank.address (WorkerArithmetic.KeccakColumnParity.native.artifact.placement index))) := by
  kernel_rfl

/-- Every native scalar gate and cache is in the complete checked typed gate list. -/
theorem complete : WorkerArithmetic.KeccakColumnParity.native.selected = List.finRange WorkerArithmetic.KeccakColumnParity.native.artifact.gates.length := by
  kernel_rfl

/-- A satisfying description assignment extends to the cached physical layers and retains every source value. -/
theorem extension (logical : Nat → F)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.KeccakColumnParity.imported.circuit)) :
    ∃ physical : GKRAddress → F, Holds Captures.KeccakColumnParity.imported.circuit physical ∧
      PlacementAgreement Captures.KeccakColumnParity.imported.circuit physical logical := by
  rw [← WorkerBindings.KeccakColumnParity.description] at holds
  have source := DescriptionBridge.source_of_assertions _ logical holds
  apply DescriptionBridge.extension Captures.KeccakColumnParity.imported.circuit WorkerArithmetic.KeccakColumnParity.native.artifact WorkerArithmetic.KeccakColumnParity.native.selected WorkerArithmetic.KeccakColumnParity.native.extension
    WorkerArithmetic.KeccakColumnParity.native.certificate WorkerArithmetic.KeccakColumnParity.native.gatesChecked WorkerArithmetic.KeccakColumnParity.native.checked complete bank
    (WireBank.ofList_roundTrip _ _ unique) ?_ ?_ logical source
  · intro entry member
    have listed : entry ∈ (Captures.KeccakColumnParity.imported.circuit).placement_data.entries.toList := by simpa using member
    rw [placement_binding] at listed
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp listed
    exact ⟨index, rfl, rfl⟩
  · intro physical gates
    apply WorkerBindings.KeccakColumnParity.native_holds physical
    have same : (fun index => physical WorkerBindings.KeccakColumnParity.addresses[index]) =
        physical ∘ bank.address := by
      funext index
      exact congrArg physical (coordinate index).symm
    rw [same]
    exact gates

end Airbender.Compiler.WorkerExtension.KeccakColumnParity
