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
theorem binding16 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate16 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[59]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate16 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate16.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate16.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨16, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding16 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨59, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause16 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[59]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate16.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨16, by decide⟩)
  exact (binding16 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨16, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding17 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate17 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[60]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate17 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate17.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate17.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨17, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding17 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨60, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause17 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[60]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate17.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨17, by decide⟩)
  exact (binding17 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨17, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding18 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate18 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[61]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate18 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate18.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate18.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨18, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding18 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨61, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause18 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[61]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate18.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨18, by decide⟩)
  exact (binding18 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨18, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding19 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate19 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[62]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate19 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate19.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate19.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨19, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding19 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨62, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause19 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[62]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate19.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨19, by decide⟩)
  exact (binding19 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨19, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding20 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate20 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[63]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate20 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate20.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate20.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨20, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding20 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨63, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause20 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[63]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate20.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨20, by decide⟩)
  exact (binding20 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨20, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding21 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate21 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[64]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate21 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate21.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate21.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨21, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding21 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨64, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause21 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[64]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate21.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨21, by decide⟩)
  exact (binding21 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨21, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding22 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate22 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[65]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate22 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate22.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate22.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨22, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding22 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨65, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause22 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[65]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate22.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨22, by decide⟩)
  exact (binding22 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨22, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding23 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate23 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[66]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate23 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate23.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate23.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨23, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding23 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨66, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause23 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[66]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate23.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨23, by decide⟩)
  exact (binding23 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨23, by decide⟩)))
theorem gates002 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate16, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate17, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate18, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate19, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate20, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate21, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate22, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate23], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate16 physical accepted) (cons_holds (gate17 physical accepted) (cons_holds (gate18 physical accepted) (cons_holds (gate19 physical accepted) (cons_holds (gate20 physical accepted) (cons_holds (gate21 physical accepted) (cons_holds (gate22 physical accepted) (cons_holds (gate23 physical accepted) (by intro gate member; cases member)))))))))

theorem clauses002 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[59]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[60]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[61]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[62]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[63]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[64]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[65]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[66]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (clause16 physical holds) (cons_zero (clause17 physical holds) (cons_zero (clause18 physical holds) (cons_zero (clause19 physical holds) (cons_zero (clause20 physical holds) (cons_zero (clause21 physical holds) (cons_zero (clause22 physical holds) (cons_zero (clause23 physical holds) (by intro clause member; cases member)))))))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
