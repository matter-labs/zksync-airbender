module
public import Proven.Compiler.WorkerArithmetic.KeccakThetaRho
public import Human.Compiler.Captures.KeccakThetaRho
public import Proven.Compiler.DescriptionBridge
public import Proven.Compiler.WorkerBindings.KeccakThetaRho.Data
public import Proven.Compiler.Reverse
public import Proven.KernelExact
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakThetaRho
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding24 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate24 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[67]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate24 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate24.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate24.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨24, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding24 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨67, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause24 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[67]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate24.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨24, by decide⟩)
  exact (binding24 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨24, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding25 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate25 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[68]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate25 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate25.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate25.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨25, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding25 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨68, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause25 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[68]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate25.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨25, by decide⟩)
  exact (binding25 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨25, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding26 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate26 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[69]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate26 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate26.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate26.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨26, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding26 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨69, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause26 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[69]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate26.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨26, by decide⟩)
  exact (binding26 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨26, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding27 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate27 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[70]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate27 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate27.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate27.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨27, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding27 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨70, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause27 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[70]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate27.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨27, by decide⟩)
  exact (binding27 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨27, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding28 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate28 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[71]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate28 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate28.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate28.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨28, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding28 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨71, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause28 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[71]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate28.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨28, by decide⟩)
  exact (binding28 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨28, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding29 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate29 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[72]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate29 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate29.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate29.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨29, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding29 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨72, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause29 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[72]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate29.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨29, by decide⟩)
  exact (binding29 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨29, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding30 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate30 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[73]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate30 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate30.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate30.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨30, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding30 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨73, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause30 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[73]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate30.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨30, by decide⟩)
  exact (binding30 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨30, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding31 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate31 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[74]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate31 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate31.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate31.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨31, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding31 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨74, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause31 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[74]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate31.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨31, by decide⟩)
  exact (binding31 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨31, by decide⟩)))
theorem gates003 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate24, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate25, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate26, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate27, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate28, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate29, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate30, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate31], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate24 physical accepted) (cons_holds (gate25 physical accepted) (cons_holds (gate26 physical accepted) (cons_holds (gate27 physical accepted) (cons_holds (gate28 physical accepted) (cons_holds (gate29 physical accepted) (cons_holds (gate30 physical accepted) (cons_holds (gate31 physical accepted) (by intro gate member; cases member)))))))))

theorem clauses003 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[67]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[68]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[69]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[70]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[71]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[72]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[73]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[74]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (clause24 physical holds) (cons_zero (clause25 physical holds) (cons_zero (clause26 physical holds) (cons_zero (clause27 physical holds) (cons_zero (clause28 physical holds) (cons_zero (clause29 physical holds) (cons_zero (clause30 physical holds) (cons_zero (clause31 physical holds) (by intro clause member; cases member)))))))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
