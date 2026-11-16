module
public import Proven.Compiler.DescriptionExtension
public import Proven.Compiler.WorkerBindings.KeccakThetaRho

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerExtension.KeccakThetaRho
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 32768

/-- The complete typed address bank has no repeated physical address. -/
theorem unique : WorkerBindings.KeccakThetaRho.addresses.toList.Nodup := by decide +kernel

/-- The finite bank covers all physical coordinates of the checked arithmetic artifact. -/
def bank : WireBank 207 :=
  WireBank.ofList WorkerBindings.KeccakThetaRho.addresses.toList (by decide)

/-- The bank and the vector use the same physical coordinate. -/
theorem coordinate (index : Fin 207) :
    bank.address index = WorkerBindings.KeccakThetaRho.addresses[index] := by
  exact List.get_eq_getElem.trans (Vector.getElem_toList _)

/-- Each source index is bound to its actual captured physical location. -/
theorem placement_binding : (Captures.KeccakThetaRho.imported.circuit).placement_data.entries.toList =
    List.ofFn (fun index : Fin 199 => (index.val, bank.address (WorkerArithmetic.KeccakThetaRho.native.artifact.placement index))) := by
  kernel_rfl

/-- Every native scalar gate and cache is in the complete checked typed gate list. -/
theorem complete : WorkerArithmetic.KeccakThetaRho.native.selected = List.finRange WorkerArithmetic.KeccakThetaRho.native.artifact.gates.length := by
  kernel_rfl

/-- A satisfying description assignment extends to the cached physical layers and retains every source value. -/
theorem extension (logical : Nat → F)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.KeccakThetaRho.imported.circuit)) :
    ∃ physical : GKRAddress → F, Holds Captures.KeccakThetaRho.imported.circuit physical ∧
      PlacementAgreement Captures.KeccakThetaRho.imported.circuit physical logical := by
  rw [← WorkerBindings.KeccakThetaRho.description] at holds
  have source := DescriptionBridge.source_of_assertions _ logical holds
  apply DescriptionBridge.extension Captures.KeccakThetaRho.imported.circuit WorkerArithmetic.KeccakThetaRho.native.artifact WorkerArithmetic.KeccakThetaRho.native.selected WorkerArithmetic.KeccakThetaRho.native.extension
    WorkerArithmetic.KeccakThetaRho.native.certificate WorkerArithmetic.KeccakThetaRho.native.gatesChecked WorkerArithmetic.KeccakThetaRho.native.checked complete bank
    (WireBank.ofList_roundTrip _ _ unique) ?_ ?_ logical source
  · intro entry member
    have listed : entry ∈ (Captures.KeccakThetaRho.imported.circuit).placement_data.entries.toList := by simpa using member
    rw [placement_binding] at listed
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp listed
    exact ⟨index, rfl, rfl⟩
  · intro physical gates
    apply WorkerBindings.KeccakThetaRho.native_holds physical
    have same : (fun index => physical WorkerBindings.KeccakThetaRho.addresses[index]) =
        physical ∘ bank.address := by
      funext index
      exact congrArg physical (coordinate index).symm
    rw [same]
    exact gates

end Airbender.Compiler.WorkerExtension.KeccakThetaRho
