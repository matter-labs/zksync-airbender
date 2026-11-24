module
public import Proven.Compiler.DescriptionExtension
public import Proven.Compiler.WorkerBindings.KeccakChi5

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerExtension.KeccakChi5
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 32768

/-- The complete typed address bank has no repeated physical address. -/
theorem unique : WorkerBindings.KeccakChi5.addresses.toList.Nodup := by decide +kernel

/-- The finite bank covers all physical coordinates of the checked arithmetic artifact. -/
def bank : WireBank 196 :=
  WireBank.ofList WorkerBindings.KeccakChi5.addresses.toList (by decide)

/-- The bank and the vector use the same physical coordinate. -/
theorem coordinate (index : Fin 196) :
    bank.address index = WorkerBindings.KeccakChi5.addresses[index] := by
  exact List.get_eq_getElem.trans (Vector.getElem_toList _)

/-- Each source index is bound to its actual captured physical location. -/
theorem placement_binding : (Captures.KeccakChi5.imported.circuit).placement_data.entries.toList =
    List.ofFn (fun index : Fin 189 => (index.val, bank.address (WorkerArithmetic.KeccakChi5.native.artifact.placement index))) := by
  kernel_rfl

/-- Every native scalar gate and cache is in the complete checked typed gate list. -/
theorem complete : WorkerArithmetic.KeccakChi5.native.selected = List.finRange WorkerArithmetic.KeccakChi5.native.artifact.gates.length := by
  kernel_rfl

/-- A satisfying description assignment extends to the cached physical layers and retains every source value. -/
theorem extension (logical : Nat → F)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.KeccakChi5.imported.circuit)) :
    ∃ physical : GKRAddress → F, Holds Captures.KeccakChi5.imported.circuit physical ∧
      PlacementAgreement Captures.KeccakChi5.imported.circuit physical logical := by
  rw [← WorkerBindings.KeccakChi5.description] at holds
  have source := DescriptionBridge.source_of_assertions _ logical holds
  apply DescriptionBridge.extension Captures.KeccakChi5.imported.circuit WorkerArithmetic.KeccakChi5.native.artifact WorkerArithmetic.KeccakChi5.native.selected WorkerArithmetic.KeccakChi5.native.extension
    WorkerArithmetic.KeccakChi5.native.certificate WorkerArithmetic.KeccakChi5.native.gatesChecked WorkerArithmetic.KeccakChi5.native.checked complete bank
    (WireBank.ofList_roundTrip _ _ unique) ?_ ?_ logical source
  · intro entry member
    have listed : entry ∈ (Captures.KeccakChi5.imported.circuit).placement_data.entries.toList := by simpa using member
    rw [placement_binding] at listed
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp listed
    exact ⟨index, rfl, rfl⟩
  · intro physical gates
    apply WorkerBindings.KeccakChi5.native_holds physical
    have same : (fun index => physical WorkerBindings.KeccakChi5.addresses[index]) =
        physical ∘ bank.address := by
      funext index
      exact congrArg physical (coordinate index).symm
    rw [same]
    exact gates

end Airbender.Compiler.WorkerExtension.KeccakChi5
