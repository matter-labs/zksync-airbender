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
theorem binding32 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate32 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[75]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate32 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate32.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate32.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨32, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding32 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨75, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause32 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[75]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate32.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨32, by decide⟩)
  exact (binding32 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨32, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding33 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate33 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[76]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate33 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate33.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate33.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨33, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding33 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨76, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause33 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[76]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate33.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨33, by decide⟩)
  exact (binding33 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨33, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding34 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate34 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[77]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate34 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate34.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate34.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨34, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding34 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨77, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause34 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[77]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate34.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨34, by decide⟩)
  exact (binding34 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨34, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding35 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate35 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[78]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate35 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate35.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate35.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨35, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding35 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨78, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause35 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[78]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate35.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨35, by decide⟩)
  exact (binding35 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨35, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding36 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate36 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[79]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate36 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate36.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate36.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨36, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding36 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨79, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause36 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[79]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate36.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨36, by decide⟩)
  exact (binding36 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨36, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding37 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate37 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[80]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate37 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate37.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate37.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨37, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding37 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨80, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause37 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[80]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate37.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨37, by decide⟩)
  exact (binding37 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨37, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding38 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate38 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[81]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate38 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate38.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate38.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨38, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding38 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨81, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause38 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[81]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate38.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨38, by decide⟩)
  exact (binding38 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨38, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding39 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate39 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate39 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate39.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate39.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨39, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding39 physical).trans (gate_at accepted ⟨1, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause39 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate39.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨39, by decide⟩)
  exact (binding39 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨39, by decide⟩)))
theorem gates004 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate32, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate33, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate34, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate35, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate36, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate37, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate38, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate39], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate32 physical accepted) (cons_holds (gate33 physical accepted) (cons_holds (gate34 physical accepted) (cons_holds (gate35 physical accepted) (cons_holds (gate36 physical accepted) (cons_holds (gate37 physical accepted) (cons_holds (gate38 physical accepted) (cons_holds (gate39 physical accepted) (by intro gate member; cases member)))))))))

theorem clauses004 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[75]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[76]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[77]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[78]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[79]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[80]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[81]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (clause32 physical holds) (cons_zero (clause33 physical holds) (cons_zero (clause34 physical holds) (cons_zero (clause35 physical holds) (cons_zero (clause36 physical holds) (cons_zero (clause37 physical holds) (cons_zero (clause38 physical holds) (cons_zero (clause39 physical holds) (by intro clause member; cases member)))))))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
